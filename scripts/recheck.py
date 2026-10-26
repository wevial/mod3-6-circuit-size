"""recheck.py: re-solve the CNFs that `CnfRuns.mod3_6_size_13`'s 22 hypotheses name, and check every
proof with two verified checkers. Python 3.9+, standard library only. reproduce.sh calls it; the
paths below are relative to the repository, and the work directory is $M36_WORK (default ./work).

    recheck.py prepare                 export each split run's base CNFs with cnfexport
    recheck.py audit                   check results/mac_recheck_results.tsv line by line
    recheck.py controls                both checkers must reject altered proofs, explicitly
    recheck.py run quick [--seed S] [--leaves N] [--workers N]
    recheck.py run full [--hardest K] [--workers N]
    recheck.py summary <results.tsv>

`run quick` does all 92 scan CNFs and a seeded uniform sample of N of the 13,347 leaves (default
134, 1%), drawn as `random.Random(sha256(S)).sample(range(13347), N)` over the leaves in
`cnfexport list` order. `run full` does every CNF, 13,439 in all; `--hardest K` restricts it to the
K leaves with the largest recorded solve+check time.

For each CNF: `cnfexport` writes the DIMACS (a scan with `cnfexport scan`; a leaf as header + base
body + cube lines, which `CnfRuns.dimacs_append` proves is the leaf's DIMACS). Its sha256 must equal
the one recorded for it (a ledger line marked `UNSAT certified` with the same cube, or for a scan
`cnf_certify.out`). CaDiCaL writes a binary LRAT proof and must exit 20. Then:

* cake_lpr (CakeML, verified down to machine code, DIMACS parser included) checks the proof against
  the DIMACS file. It exits 0 on failure too, so only stdout exactly `s VERIFIED UNSAT\\n` (with exit
  0) counts.
* lratdirect (Lean, `Garden/LratDirect.lean`, `check_sound`) checks it against the CNF it builds in
  memory from `CnfSpecs`; only exit 0 with exactly one stdout line starting
  `s VERIFIED UNSAT (<job label>: ` counts.

A CNF is OK only if all four hold. The proof is then deleted.

Differences from the driver as run on the Mac (results/as-run/mac_recheck.py), which fix the three
weaknesses its review found:
1. Resuming validates every field of every earlier line (job, sha256, CaDiCaL exit, both verdicts,
   session pins) and refuses to resume on any line it cannot validate; it no longer trusts a line
   just because it ends in OK. `summary` applies the same validation.
2. A control counts only an explicit rejection: cake_lpr exit 0, nothing on stdout and stderr
   `c Checking failed…`; lratdirect exit 1 with one line `s NOT VERIFIED (… <job>: …`. A crash, a
   signal or any other output is INCONCLUSIVE and fails the controls.
3. The disk check tolerates a proof deleted between listing and measuring it (counting it as not yet
   written, which reserves more space, never less).
Also: cake_lpr must exit 0 as well as print exactly `s VERIFIED UNSAT`. A FAIL line stops the run;
rerunning the command retries that CNF, and a later valid OK line for it supersedes the FAIL (both
are reported by `summary`).
"""
import ast, calendar, hashlib, math, os, random, re, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
W = os.path.abspath(os.environ.get('M36_WORK') or os.path.join(ROOT, 'work'))
BIN = os.path.join(ROOT, 'lean/direct/.lake/build/bin')
EXPORT, DIRECT = os.path.join(BIN, 'cnfexport'), os.path.join(BIN, 'lratdirect')
CADICAL = os.path.join(W, 'tools/cadical/build/cadical')
CAKE = os.path.join(W, 'tools/cake_lpr/cake_lpr')
LEDGERS = os.path.join(ROOT, 'results/ledgers')
CERTIFY_OUT = os.path.join(ROOT, 'results/cnf_certify.out')
MAC_RESULTS = os.path.join(ROOT, 'results/mac_recheck_results.tsv')
BASES = os.path.join(W, 'bases')
TMP = os.path.join(W, 'tmp')
# cake_lpr's RSS is its heap (CakeML's GC grows into all of it). The hardest leaf (full6_12 10397,
# 2.2 GB proof) passed at 1024 MB; 2048 MB is twice that (results/mac_recheck_probe.out).
CAKE_HEAP_MB, CAKE_STACK_MB = 2048, 4096
WORKER_PEAK_MIB = 2100           # bounds cake_lpr (its heap); a worker runs its processes one after another
OTHER_PEAK_MIB = 800             # bounds CaDiCaL and lratdirect (peaks on the Mac: 431 and 688 MiB)
RESERVE_MIB = 1024               # for the driver and the page cache
DISK_FLOOR = int(float(os.environ.get('M36_DISK_FLOOR_GB', '10')) * 1e9)
CAKE_ENV = dict(os.environ, CML_HEAP_SIZE=str(CAKE_HEAP_MB), CML_STACK_SIZE=str(CAKE_STACK_MB))
TOTAL_LEAVES = 13347

LEDGER = {   # split run (cnfexport name) -> ledger file for (tag, depth)
    'cube5_0': lambda tag, s: 'ledger_mod3_5_0_9_s2.txt',
    'cube5_2': lambda tag, s: 'ledger_mod3_5_2_9_s2.txt',
    'w2cube_8': lambda tag, s: 'ledger_w2_5_1_8_w2_s1.txt',
    'w2cube_9': lambda tag, s: 'ledger_w2_5_1_9_w2_s1.txt',
    'full6_12': lambda tag, s: 'ledger_mod3_6_1_12_s%d_elim2_sem12%s.txt' % (s, ['_x', '_x_S', '_x_S_E'][tag]),
}
COLUMNS = ['kind', 'run', 'i', 'record', 'sha256', 'sha', 'cadical', 'solve_s', 'solve_cpu', 'solve_MiB',
           'proof_MB', 'cake', 'cake_s', 'cake_cpu', 'cake_MiB', 'lratdirect', 'direct_s', 'direct_cpu',
           'direct_MiB', 'recorded_s', 'start', 'end', 'verdict']
CAKE_OK = 's VERIFIED UNSAT'


def est_proof_bytes(rec):
    """Upper estimate of a proof's size from the ledger's solve+check seconds (measured: 2.3-2.9 MB/s)."""
    return 4e6 * rec + 50e6


def utc(t):
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t))


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def proc(cmd, d, env=None):
    """Run cmd (stderr to a file in d); return (exit code, stdout bytes, stderr text (its first 2,000
    characters), wall s, cpu s, peak RSS MiB). CPU time and peak RSS come from wait4 on that process."""
    err = os.path.join(d, 'stderr')
    t0 = time.time()
    with open(err, 'wb') as e:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=e, stdin=subprocess.DEVNULL, env=env)
        out = p.stdout.read()
        _, status, ru = os.wait4(p.pid, 0)
    p.stdout.close()
    code = os.waitstatus_to_exitcode(status)
    with open(err, 'rb') as e:
        errtext = e.read(2000).decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rss = ru.ru_maxrss / (2**20 if sys.platform == 'darwin' else 2**10)
    return code, out, errtext, time.time() - t0, ru.ru_utime + ru.ru_stime, rss


def one_line(out):
    """stdout as text if it is exactly one newline-terminated line, else None."""
    text = out.decode(errors='replace')
    return text[:-1] if text.endswith('\n') and text.count('\n') == 1 else None


def cake_verdict(code, out, err):
    """(accepted, explicitly rejected, text). Accepted: exit 0 and stdout exactly `s VERIFIED UNSAT\\n`.
    Explicit rejection: exit 0, nothing on stdout, and stderr starting `c Checking failed` (cake_lpr's
    message for a proof step that fails)."""
    ok = code == 0 and out == (CAKE_OK + '\n').encode()
    if ok:
        return True, False, CAKE_OK
    text = out.decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rejected = code == 0 and out == b'' and err.startswith('c Checking failed')
    return False, rejected, '%s exit %d: %s' % ('REJECTED' if rejected else 'INCONCLUSIVE', code,
                                                (text or err)[:200] or '(no output)')


def direct_verdict(code, out, err, label):
    """(accepted, explicitly rejected, text). Accepted: exit 0, one line `s VERIFIED UNSAT (<label>: …`.
    Explicit rejection: exit 1, one line `s NOT VERIFIED (… <label>: …`."""
    line = one_line(out)
    ok = code == 0 and line is not None and line.startswith('s VERIFIED UNSAT (%s: ' % label)
    if ok:
        return True, False, line.replace('\t', ' ')
    rejected = code == 1 and line is not None and line.startswith('s NOT VERIFIED (') and \
        ('; %s: ' % label) in line
    text = out.decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    return False, rejected, '%s exit %d: %s' % ('REJECTED' if rejected else 'INCONCLUSIVE', code,
                                                (text or err)[:300] or '(no output)')


# ---------------------------------------------------------------- jobs

def hypotheses():
    """The theorem's 22 hypotheses as Lean lists them: scans (name, lo, hi), splits (name, r, count)."""
    out = subprocess.run([EXPORT, 'list'], capture_output=True, text=True, check=True).stdout
    scans, splits = [], []
    for line in out.splitlines():
        kind, name, a, b = line.split('\t')
        (scans if kind == 'scan' else splits).append((name, int(a), int(b)))
    assert len(scans) == 17 and len(splits) == 5 and sorted(n for n, _, _ in splits) == sorted(LEDGER), out
    assert sum(c for _, _, c in splits) == TOTAL_LEAVES and sum(b - a + 1 for _, a, b in scans) == 92, out
    return scans, splits


def ledger(path):
    """idx -> [(sha256, recorded solve+check s, cube)] for every line `UNSAT certified` with
    lratcheck's verdict."""
    out = {}
    for line in open(os.path.join(LEDGERS, path)):
        t = line.rstrip('\n').split('\t')
        if len(t) < 7 or t[2] != 'UNSAT' or t[3] != 'certified' or not t[5].startswith('s VERIFIED UNSAT'):
            continue
        m = re.search(r'solve\+check=([\d.]+)s', t[4])
        out.setdefault(int(t[0]), []).append((t[6], float(m.group(1)) if m else 0.0, ast.literal_eval(t[1])))
    return out


def recorded_scans():
    """(name, r) -> (sha256, seconds) as cnf_certify.out recorded them."""
    out = {}
    for line in open(CERTIFY_OUT):
        m = re.match(r'\s+(\S+) r=(\d+): sha256 ([0-9a-f]{64}) .*\[([0-9.]+)s\]$', line.rstrip('\n'))
        if m:
            out[m.group(1), int(m.group(2))] = (m.group(3), float(m.group(4)))
    return out


def prepare():
    _, splits = hypotheses()
    for name, _, count in splits:
        d = os.path.join(BASES, name)
        if os.path.exists(os.path.join(d, 'manifest.tsv')):
            print(name, 'already exported')
            continue
        os.makedirs(d, exist_ok=True)
        man = subprocess.run([EXPORT, 'leaves', name, d], capture_output=True, text=True, check=True).stdout
        assert len(man.splitlines()) == count, (name, len(man.splitlines()), count)
        with open(os.path.join(d, 'manifest.tsv.part'), 'w') as f:
            f.write(man)
        os.replace(os.path.join(d, 'manifest.tsv.part'), os.path.join(d, 'manifest.tsv'))
        print(name, count, 'leaves exported', flush=True)


def jobs():
    """Every CNF the hypotheses name: scans in `cnfexport list` order, then leaves in list order
    (`pos` is a leaf's position among all 13,347). Each job carries the label lratdirect prints and
    the sha256 values its DIMACS may have."""
    scans, splits = hypotheses()
    rec = recorded_scans()
    out = []
    for name, lo, hi in scans:
        for r in range(lo, hi + 1):
            sha, secs = rec[name, r]
            out.append(dict(kind='scan', run=name, i=r, label='scan %s r=%d' % (name, r), want={sha},
                            record='cnf_certify.out', rec=secs))
    ledgers, pos = {}, 0
    for name, _, count in splits:
        rows = open(os.path.join(BASES, name, 'manifest.tsv')).read().splitlines()
        assert len(rows) == count, name
        for n, row in enumerate(rows):
            p, tag, split, idx, hdr, cube = row.split('\t')
            p, tag, split, idx = int(p), int(tag), int(split), int(idx)
            assert p == n, 'manifest out of order'
            lf = LEDGER[name](tag, split)
            if lf not in ledgers:
                ledgers[lf] = ledger(lf)
            lits = [int(c.split()[0]) for c in cube.split('|') if c]
            hits = [(sha, secs) for sha, secs, cb in ledgers[lf].get(idx, []) if cb == lits]
            out.append(dict(kind='leaf', run=name, i=p, tag=tag, label='leaf %s %d' % (name, p), pos=pos,
                            hdr=hdr, cube=cube, want={s for s, _ in hits}, record='%s:%d' % (lf, idx),
                            rec=max([t for _, t in hits] or [0.0])))
            pos += 1
    assert pos == TOTAL_LEAVES
    return out


def key(j):
    return (j['kind'], j['run'], j['i'])


BODIES, BODY_LOCK = {}, threading.Lock()


def body(run, tag):
    with BODY_LOCK:
        if (run, tag) not in BODIES:
            BODIES[run, tag] = open(os.path.join(BASES, run, 'base%d.body' % tag), 'rb').read()
        return BODIES[run, tag]


def write_cnf(j, path):
    if j['kind'] == 'scan':
        subprocess.run([EXPORT, 'scan', j['run'], str(j['i']), path], check=True)
    else:
        with open(path, 'wb') as f:
            f.write(j['hdr'].encode() + b'\n')
            f.write(body(j['run'], j['tag']))
            f.write(j['cube'].replace('|', '\n').encode())


def direct_args(j):
    return [j['kind'], j['run'], str(j['i'])]


RUNNING = {}          # key -> proof path, for the disk estimate


def run_job(j):
    """Export, sha256, solve, check twice; return the result line's fields."""
    d = tempfile.mkdtemp(dir=TMP, prefix='job-')
    t0 = time.time()
    try:
        cnf, proof = os.path.join(d, 'f.cnf'), os.path.join(d, 'proof.lrat')
        RUNNING[key(j)] = proof
        write_cnf(j, cnf)
        h = sha256(cnf)
        sha_ok = h in j['want']
        c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof], d)
        size = os.path.getsize(proof) if os.path.exists(proof) else 0
        none = (False, False, 'not run', 0.0, 0.0, 0.0)
        cake = direct = none
        if sha_ok and c[0] == 20:
            with CAKE_SLOTS:
                k = proc([CAKE, cnf, proof], d, CAKE_ENV)
            cake = cake_verdict(k[0], k[1], k[2]) + k[3:]
            x = proc([DIRECT] + direct_args(j) + [proof], d)
            direct = direct_verdict(x[0], x[1], x[2], j['label']) + x[3:]
        ok = sha_ok and c[0] == 20 and cake[0] and direct[0]
        return [j['kind'], j['run'], j['i'], j['record'], h,
                ('= ' + ('ledger' if j['kind'] == 'leaf' else 'cnf_certify.out')) if sha_ok else 'MISMATCH',
                'exit %d' % c[0] if c[0] == 20 else 'exit %d: %s' % (c[0], c[2][:200]),
                '%.1f' % c[3], '%.1f' % c[4], '%.0f' % c[5], '%.1f' % (size / 1e6),
                cake[2], '%.1f' % cake[3], '%.1f' % cake[4], '%.0f' % cake[5],
                direct[2], '%.1f' % direct[3], '%.1f' % direct[4], '%.0f' % direct[5],
                '%.1f' % j['rec'], utc(t0), utc(time.time()), 'OK' if ok else 'FAIL']
    finally:
        RUNNING.pop(key(j), None)
        shutil.rmtree(d, ignore_errors=True)


# ---------------------------------------------------------------- validation of result lines

def valid_ok_row(t, by, mac=False):
    """Why a line marked OK is not a valid OK line for a job in `by` (None if it is). `mac`: the Mac's
    record, whose lratdirect field is normalized to `s VERIFIED UNSAT (<n> actions)`."""
    if len(t) != len(COLUMNS):
        return 'has %d fields, not %d' % (len(t), len(COLUMNS))
    r = dict(zip(COLUMNS, t))
    try:
        k = (r['kind'], r['run'], int(r['i']))
    except ValueError:
        return 'bad index'
    j = by.get(k)
    if j is None:
        return 'not a job of the theorem'
    if r['record'] != j['record']:
        return 'record %s, expected %s' % (r['record'], j['record'])
    if r['sha256'] not in j['want']:
        return 'sha256 is not the recorded one'
    if r['sha'] != '= ' + ('ledger' if j['kind'] == 'leaf' else 'cnf_certify.out'):
        return 'sha field %r' % r['sha']
    if r['cadical'] != 'exit 20':
        return 'CaDiCaL %r' % r['cadical']
    if r['cake'] != CAKE_OK:
        return 'cake_lpr %r' % r['cake']
    if not (re.fullmatch(r's VERIFIED UNSAT \(%s: .*\)' % re.escape(j['label']), r['lratdirect'])
            or mac and re.fullmatch(r's VERIFIED UNSAT \(\d+ actions\)', r['lratdirect'])):
        return 'lratdirect %r' % r['lratdirect']
    for c in ('solve_s', 'solve_cpu', 'solve_MiB', 'proof_MB', 'cake_s', 'cake_cpu', 'cake_MiB',
              'direct_s', 'direct_cpu', 'direct_MiB', 'recorded_s'):
        try:
            v = float(r[c])
        except ValueError:
            return '%s %r' % (c, r[c])
        if not (math.isfinite(v) and v >= 0):
            return '%s %r' % (c, r[c])
    try:
        t0, t1 = (calendar.timegm(time.strptime(r[c], '%Y-%m-%dT%H:%M:%SZ')) for c in ('start', 'end'))
    except ValueError:
        return 'start/end %r %r' % (r['start'], r['end'])
    if t1 < t0:
        return 'ends before it starts'
    return None


def read_results(path, by, pins):
    """Parse and validate a results file written by `run`. Return (ok, superseded, fails, sessions):
    ok maps each job to its valid OK line; superseded are FAIL lines followed by a valid OK line for
    the same job; fails are the other FAIL lines. Raises SystemExit unless every line is a column
    header, a session or end line, a valid OK line or a FAIL line; every result line follows a session
    header run under `pins` (the sha256 of this script, the binaries, the ledgers and the bases); and
    no job has two OK lines."""
    ok, failed, sessions, bad, in_session = {}, {}, [], [], False
    for n, line in enumerate(open(path), 1):
        line = line.rstrip('\n')
        if line.startswith('# session'):
            sessions.append(line)
            m = re.search(r' pins ([0-9a-f]{64}) ', line)
            if not m or m.group(1) != pins:
                raise SystemExit('%s:%d: this session ran under other pins (a binary, the script, a ledger '
                                 'or a base differs from now); use a new results file' % (path, n))
            in_session = True
            continue
        if line.startswith('# end'):
            sessions.append(line)
            continue
        if line.startswith('#') or not line:
            continue
        t = line.split('\t')
        if not in_session:
            bad.append('%s:%d: result line before any session header' % (path, n))
            continue
        if t[-1] == 'OK':
            why = valid_ok_row(t, by)
            k = (t[0], t[1], int(t[2])) if not why else None
            if why:
                bad.append('%s:%d: %s' % (path, n, why))
            elif k in ok:
                bad.append('%s:%d: a second OK line for %s %s %s' % ((path, n) + k))
            else:
                ok[k] = t
        elif t[-1] == 'FAIL' and len(t) == len(COLUMNS):
            failed.setdefault((t[0], t[1], t[2]), []).append(t)
        else:
            bad.append('%s:%d: not a result line' % (path, n))
    if bad:
        raise SystemExit('lines that do not validate:\n  ' + '\n  '.join(bad[:20]))
    superseded, fails = [], []
    for k, rows in failed.items():
        later = k[2].isdigit() and (k[0], k[1], int(k[2])) in ok
        (superseded if later else fails).extend(rows)
    return ok, superseded, fails, sessions


# ---------------------------------------------------------------- pins of this session

def pins_text():
    files = [CADICAL, CAKE, DIRECT, EXPORT, os.path.abspath(__file__), CERTIFY_OUT]
    files += sorted(os.path.join(LEDGERS, f) for f in os.listdir(LEDGERS))
    for run in sorted(os.listdir(BASES)):
        files += sorted(os.path.join(BASES, run, f) for f in os.listdir(os.path.join(BASES, run)))
    return ''.join('%s  %s\n' % (sha256(p), os.path.relpath(p, ROOT if p.startswith(ROOT + os.sep) else W))
                   for p in files)


# ---------------------------------------------------------------- resources

def cgroup_cpus():
    try:
        q, p = open('/sys/fs/cgroup/cpu.max').read().split()
        if q != 'max':
            return max(1, int(int(q) // int(p)))
    except (OSError, ValueError):
        pass
    try:
        return len(os.sched_getaffinity(0))
    except AttributeError:
        return os.cpu_count() or 1


def memory_mib():
    total = None
    try:
        total = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES') / 2**20
    except (ValueError, OSError, AttributeError):
        pass
    try:
        m = open('/sys/fs/cgroup/memory.max').read().strip()
        if m != 'max':
            total = min(total or float('inf'), int(m) / 2**20)
    except (OSError, ValueError):
        pass
    return total


def plan_memory(workers=None):
    """(workers, cake slots): at most `slots` cake_lpr processes run at once, so that
    slots * WORKER_PEAK_MIB + (workers - slots) * OTHER_PEAK_MIB fits in memory less RESERVE_MIB."""
    mem = memory_mib()
    budget = (mem - RESERVE_MIB) if mem else WORKER_PEAK_MIB
    slots = lambda w: int((budget - w * OTHER_PEAK_MIB) // (WORKER_PEAK_MIB - OTHER_PEAK_MIB))
    if workers is None:
        workers = max(1, cgroup_cpus())
        while workers > 1 and slots(workers) < 1:
            workers -= 1
    if slots(workers) < 1:
        raise SystemExit('not enough memory for %d workers (%.0f MiB): use --workers with a smaller number'
                         % (workers, mem or 0))
    return workers, min(slots(workers), workers)


CAKE_SLOTS = threading.Semaphore(1)


def free_disk():
    s = os.statvfs(W)
    return s.f_bavail * s.f_frsize


def disk_ok(j, running):
    pending = 0.0
    for r in running:
        p = RUNNING.get(key(r))
        try:
            cur = os.path.getsize(p) if p else 0
        except FileNotFoundError:    # not written yet, or deleted as its job finished: reserve it all
            cur = 0
        pending += max(0.0, est_proof_bytes(r['rec']) - cur)
    return free_disk() - pending - est_proof_bytes(j['rec']) >= DISK_FLOOR


# ---------------------------------------------------------------- run

def append(path, line):
    with open(path, 'a') as f:
        f.write(line + '\n')
        f.flush()
        os.fsync(f.fileno())


def select(all_jobs, mode, seed_hex, nleaves, hardest, quiet=False):
    """The jobs of a run. quick: every scan, and `random.Random(seed_hex).sample(range(13347), nleaves)`
    of the leaves in list order, hardest first. full: every scan, then every leaf hardest first, or
    with `hardest` only that many of the hardest leaves."""
    scans = [j for j in all_jobs if j['kind'] == 'scan']
    leaves = [j for j in all_jobs if j['kind'] == 'leaf']
    if mode == 'quick':
        pick = sorted(random.Random(seed_hex).sample(range(TOTAL_LEAVES), nleaves))
        if not quiet:
            print('seed sha256 %s; %d leaves at positions %s' % (seed_hex, nleaves, pick), flush=True)
        chosen = [leaves[p] for p in pick]
        return scans + sorted(chosen, key=lambda j: -j['rec'])
    if hardest:
        return sorted(leaves, key=lambda j: (-j['rec'], j['pos']))[:hardest]
    return scans + sorted(leaves, key=lambda j: (-j['rec'], j['pos']))


def run(mode, results, workers, seed, nleaves, hardest):
    seed_hex = hashlib.sha256(seed.encode()).hexdigest() if mode == 'quick' else '0' * 64
    global CAKE_SLOTS
    workers, slots = plan_memory(workers)
    CAKE_SLOTS = threading.Semaphore(slots)
    all_jobs = jobs()
    by = {key(j): j for j in all_jobs}
    pins = hashlib.sha256(pins_text().encode()).hexdigest()
    for d in os.listdir(TMP):                      # a killed session's temp dirs
        if d.startswith('job-'):
            shutil.rmtree(os.path.join(TMP, d), ignore_errors=True)
    done = {}
    if os.path.exists(results):
        done, _, _, sessions = read_results(results, by, pins)
        if sessions and session_selection(sessions) != (mode, seed_hex, nleaves, hardest):
            raise SystemExit('%s holds a different selection of jobs; use another --results file' % results)
    want = select(all_jobs, mode, seed_hex, nleaves, hardest)
    todo = [j for j in want if key(j) not in done]
    if not os.path.exists(results):
        append(results, '# ' + '\t'.join(COLUMNS))
    append(results, '# session %s pid %d pins %s mode %s seed_sha256 %s leaves %d hardest %d workers %d '
           'cake_slots %d cake_heap_MB %d (seed %r): %d of %d done, %d to do'
           % (utc(time.time()), os.getpid(), pins, mode, seed_hex, nleaves, hardest, workers, slots, CAKE_HEAP_MB,
              seed,
              len(want) - len(todo), len(want), len(todo)))
    print('%s: %s: %d jobs, %d already done, %d to do; %d workers, at most %d cake_lpr at once (heap %d MB)'
          % (utc(time.time()), mode, len(want), len(want) - len(todo), len(todo), workers, slots, CAKE_HEAP_MB),
          flush=True)
    t_start = time.time()
    running, stop, nfail, ndone = {}, None, 0, 0
    with ThreadPoolExecutor(workers) as ex:
        while todo or running:
            for fut in [f for f in running if f.done()]:
                j = running.pop(fut)
                try:
                    f = fut.result()
                except Exception as e:             # an exception in the driver is a FAIL too
                    f = [j['kind'], j['run'], j['i'], j['record'], '-', 'driver error: %r' % e] + \
                        ['-'] * (len(COLUMNS) - 7) + ['FAIL']
                line = '\t'.join(map(str, f))
                append(results, line)
                ndone += 1
                if f[-1] != 'OK':
                    nfail += 1
                    stop = stop or 'a CNF failed: %s %s %s' % tuple(f[:3])
                    print('FAIL ' + line, flush=True)
                elif max(float(f[i]) for i in (9, 14, 18)) > WORKER_PEAK_MIB:
                    stop = stop or 'a process of %s %s %s exceeded %d MiB' % (tuple(f[:3]) + (WORKER_PEAK_MIB,))
                if ndone % 50 == 0 or not todo:
                    print('%s: %d/%d finished, %d failed' % (utc(time.time()), ndone, ndone + len(todo) + len(running),
                                                            nfail), flush=True)
            if stop is not None:
                if not running:
                    break
            else:
                while todo and len(running) < workers:
                    j = todo[0]
                    rs = list(running.values())
                    if not disk_ok(j, rs):
                        if not rs:
                            stop = 'free disk below M36_DISK_FLOOR_GB with nothing running'
                        break
                    todo.pop(0)
                    running[ex.submit(run_job, j)] = j
            time.sleep(0.5)
    why = stop or 'all done'
    append(results, '# end %s: %s; %d left; %d failed this session; %.0f s wall'
           % (utc(time.time()), why, len(todo), nfail, time.time() - t_start))
    print('%s: stopped: %s; %d left, %d failed, %.0f s wall' % (utc(time.time()), why, len(todo), nfail,
                                                               time.time() - t_start), flush=True)
    if nfail or todo:
        sys.exit(1)
    summary(results)


# ---------------------------------------------------------------- summary and audit

def session_selection(sessions):
    """(mode, seed's sha256, leaves, hardest) of the sessions in a results file, which must all agree."""
    sel = set()
    for line in sessions:
        m = re.search(r' mode (quick|full) seed_sha256 ([0-9a-f]{64}) leaves (\d+) hardest (\d+) ', line)
        if line.startswith('# session'):
            if not m:
                raise SystemExit('unreadable session line: ' + line)
            sel.add((m.group(1), m.group(2), int(m.group(3)), int(m.group(4))))
    if len(sel) != 1:
        raise SystemExit('sessions with different selections: %s' % sorted(sel))
    return sel.pop()


def summary(results):
    """Validate a results file (every line, under the current pins) and report counts, times and peak
    RSS. Every job its sessions selected must have a valid OK line; a FAIL line counts as recovered
    only if a valid OK line for the same CNF follows it."""
    all_jobs = jobs()
    by = {key(j): j for j in all_jobs}
    pins = hashlib.sha256(pins_text().encode()).hexdigest()
    ok, superseded, fails, sessions = read_results(results, by, pins)
    mode, seed, nleaves, hardest = session_selection(sessions)
    want = {key(j) for j in select(all_jobs, mode, seed, nleaves, hardest, quiet=True)}
    extra = set(ok) - want
    good = [dict(zip(COLUMNS, ok[k])) for k in want if k in ok]
    print('# summary of %s (%s): mode %s%s' % (os.path.basename(results), utc(time.time()), mode,
          (', seed sha256 %s, %d leaves' % (seed, nleaves)) if mode == 'quick' else
          (', the %d hardest leaves' % hardest) if hardest else ''))
    for kind in ('scan', 'leaf'):
        w = {k for k in want if k[0] == kind}
        if w:
            print('%s: %d/%d CNFs OK (sha256 = recorded, CaDiCaL exit 20, cake_lpr exit 0 and stdout exactly '
                  '`s VERIFIED UNSAT`, lratdirect exit 0 and one line `s VERIFIED UNSAT (<job>: …)`)'
                  % (kind, len(w & set(ok)), len(w)))
            for run_ in sorted({k[1] for k in w}):
                wr = {k for k in w if k[1] == run_}
                print('  %s: %d/%d' % (run_, len(wr & set(ok)), len(wr)))
    print('FAIL lines: %d unrecovered, %d followed by a valid OK line for the same CNF'
          % (len(fails), len(superseded)))
    for t in (fails + superseded)[:20]:
        print('  ' + '\t'.join(t))
    f = lambda c: sum(float(r[c]) for r in good)
    print('process times, hours: CaDiCaL %.2f wall / %.2f CPU; cake_lpr %.2f / %.2f; lratdirect %.2f / %.2f'
          % (f('solve_s') / 3600, f('solve_cpu') / 3600, f('cake_s') / 3600, f('cake_cpu') / 3600,
             f('direct_s') / 3600, f('direct_cpu') / 3600))
    print('proofs written and deleted: %.1f GB' % (f('proof_MB') / 1e3))
    for c, name in (('solve_MiB', 'CaDiCaL'), ('cake_MiB', 'cake_lpr'), ('direct_MiB', 'lratdirect')):
        if good:
            m = max(good, key=lambda r: float(r[c]))
            print('peak RSS, %s: %s MiB (%s %s %s)' % (name, m[c], m['kind'], m['run'], m['i']))
    print('sessions:')
    for line in sessions:
        print('  ' + line)
    missing = want - set(ok)
    if missing or fails or extra:
        print('NOT ALL OK: %d selected CNFs without a valid OK line, %d unrecovered FAIL lines, %d OK lines '
              'for CNFs not selected' % (len(missing), len(fails), len(extra)))
        sys.exit(1)
    print('ALL OK: %d/%d CNFs' % (len(want), len(want)))


def audit():
    """Check results/mac_recheck_results.tsv, the record of the full re-check on the Mac, against
    the job list derived here from cnfexport and the ledgers: exactly one valid OK line per CNF of
    the 22 hypotheses (13,439), sha256 as recorded, no FAIL line, no line for anything else."""
    all_jobs = jobs()
    by = {key(j): j for j in all_jobs}
    seen, bad = {}, []
    for n, line in enumerate(open(MAC_RESULTS), 1):
        line = line.rstrip('\n')
        if line.startswith('#'):
            continue
        t = line.split('\t')
        why = valid_ok_row(t, by, mac=True) if t[-1] == 'OK' else 'verdict %r' % t[-1]
        if why:
            bad.append('line %d: %s' % (n, why))
            continue
        k = (t[0], t[1], int(t[2]))
        if k in seen:
            bad.append('line %d: second line for %s (first at line %d)' % (n, k, seen[k]))
        seen[k] = n
    missing = [k for k in by if k not in seen]
    print('results/mac_recheck_results.tsv: %d lines for %d jobs; %d valid OK lines; %d missing; %d bad'
          % (len(seen) + len(bad), len(by), len(seen), len(missing), len(bad)))
    for b in bad[:10]:
        print('  ' + b)
    for k in missing[:10]:
        print('  missing %s' % (k,))
    if bad or missing:
        print('AUDIT FAILED')
        sys.exit(1)
    print('AUDIT OK: every CNF of the 22 hypotheses (92 scans, 13,347 leaves) has exactly one line, '
          'and each records sha256 = recorded, CaDiCaL exit 20, cake_lpr and lratdirect VERIFIED')


# ---------------------------------------------------------------- controls

def lrat_positions(path):
    """Byte offsets in a binary LRAT file: the first byte of the first literal of each added clause,
    of each hint, and of the empty clause's last hint."""
    data = open(path, 'rb').read()
    lits, hints, last_empty_hint, p, n = [], [], None, 0, len(data)

    def num(p):
        while data[p] & 0x80:
            p += 1
        return p + 1

    while p < n:
        kind = data[p]
        p += 1
        if kind == ord('a'):
            p = num(p)                              # clause id
            first, nlits = p, 0
            while data[p] != 0:
                if nlits == 0:
                    lits.append(first)
                p = num(p)
                nlits += 1
            p += 1
            last = None
            while data[p] != 0:
                hints.append(p)
                last = p
                p = num(p)
            p += 1
            if nlits == 0:
                last_empty_hint = last
        elif kind == ord('d'):
            while data[p] != 0:
                p = num(p)
            p += 1
        else:
            raise ValueError('not binary LRAT at byte %d' % (p - 1))
    return lits, hints, last_empty_hint, n


def flip(src, dst, pos, bit):
    data = bytearray(open(src, 'rb').read())
    data[pos] ^= 1 << bit
    with open(dst, 'wb') as f:
        f.write(data)


def controls():
    """Each base proof must be accepted by both checkers; then both must reject, explicitly, the
    proof given for a different CNF and the proof with one bit flipped at four places. As on the Mac:
    scan best4_0 r=6 (given as best4_1 r=6), and a full6_12 leaf (given as the next leaf, and as the
    previous leaf, which has the same header)."""
    allok = True
    by = {key(j): j for j in jobs()}
    a6844 = by['leaf', 'full6_12', 6844]
    cases = [(by['scan', 'best4_0', 6], [by['scan', 'best4_1', 6]]),
             (a6844, [by['leaf', 'full6_12', 6845], by['leaf', 'full6_12', 6843]])]
    for a, others in cases:
        d = tempfile.mkdtemp(dir=TMP, prefix='ctl-')
        try:
            fa, proof, g = (os.path.join(d, x) for x in ('a.cnf', 'proof.lrat', 'flip.lrat'))
            write_cnf(a, fa)
            c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', fa, proof], d)
            base_cake = cake_verdict(*proc([CAKE, fa, proof], d, CAKE_ENV)[:3])
            base_direct = direct_verdict(*proc([DIRECT] + direct_args(a) + [proof], d)[:3], a['label'])
            sha_a = sha256(fa) in a['want']
            ok = c[0] == 20 and base_cake[0] and base_direct[0] and sha_a
            print('base: %s (sha256 %s): cadical exit %d; cake_lpr %s; lratdirect %s -> %s'
                  % (a['label'], 'matches' if sha_a else 'MISMATCH', c[0], base_cake[2], base_direct[2],
                     'accepted by both' if ok else 'NOT ACCEPTED'), flush=True)
            allok &= ok
            for b in others:
                fb = os.path.join(d, 'b.cnf')
                write_cnf(b, fb)
                sha_b = sha256(fb) in b['want']
                k = cake_verdict(*proc([CAKE, fb, proof], d, CAKE_ENV)[:3])
                x = direct_verdict(*proc([DIRECT] + direct_args(b) + [proof], d)[:3], b['label'])
                good = k[1] and x[1] and sha_b
                print('  (1) proof of %s given as %s (%s): cake_lpr %s; lratdirect %s -> %s'
                      % (a['label'], b['label'], b['hdr'] if b['kind'] == 'leaf' else 'its own CNF', k[2], x[2],
                         'both rejected explicitly' if good else 'NOT BOTH REJECTED EXPLICITLY'), flush=True)
                allok &= good
            lits, hints, empty, n = lrat_positions(proof)
            # bit 0 of a literal's first byte is its sign; bit 1 of a hint's first byte moves it to the
            # next or previous clause id (bit 0 would make it a RAT hint, which an LPR checker may accept)
            spots = [('sign of the first literal of the added clause at 1/2 of the clauses', lits[len(lits) // 2], 0),
                     ('hint at 1/4 of the hints, id +-1', hints[len(hints) // 4], 1),
                     ('hint at 3/4 of the hints, id +-1', hints[3 * len(hints) // 4], 1),
                     ('last hint of the empty clause, id +-1', empty, 1)]
            for what, pos, bit in spots:
                flip(proof, g, pos, bit)
                k = cake_verdict(*proc([CAKE, fa, g], d, CAKE_ENV)[:3])
                x = direct_verdict(*proc([DIRECT] + direct_args(a) + [g], d)[:3], a['label'])
                good = k[1] and x[1]
                print('  (2) bit %d of byte %d of %d flipped (%s): cake_lpr %s; lratdirect %s -> %s'
                      % (bit, pos, n, what, k[2], x[2],
                         'both rejected explicitly' if good else 'NOT BOTH REJECTED EXPLICITLY'), flush=True)
                allok &= good
        finally:
            shutil.rmtree(d, ignore_errors=True)
    print('RUNTIME CONTROLS %s' % ('PASSED: each base proof accepted by both checkers, every altered one '
                                   'rejected explicitly by both' if allok else 'FAILED'), flush=True)
    sys.exit(0 if allok else 1)


def main():
    a = sys.argv[1:]
    os.makedirs(TMP, exist_ok=True)

    def opt(name, default, conv=str):
        return conv(a[a.index(name) + 1]) if name in a else default

    if a == ['prepare']:
        prepare()
    elif a == ['audit']:
        audit()
    elif a == ['controls']:
        controls()
    elif a[:1] == ['run'] and len(a) >= 2 and a[1] in ('quick', 'full'):
        mode = a[1]
        seed = opt('--seed', 'mod3-6-circuit-size')
        nleaves = opt('--leaves', 134, int) if mode == 'quick' else 0
        hardest = opt('--hardest', 0, int) if mode == 'full' else 0
        workers = opt('--workers', None, int)
        name = 'quick-%s-%d' % (hashlib.sha256(seed.encode()).hexdigest()[:12], nleaves) if mode == 'quick' \
            else ('full-hardest%d' % hardest if hardest else 'full')
        results = opt('--results', os.path.join(W, 'results-%s.tsv' % name))
        print('results file: %s' % os.path.relpath(results, ROOT), flush=True)
        run(mode, results, workers, seed, nleaves, hardest)
    elif a[:1] == ['summary'] and len(a) == 2:
        summary(a[1])
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
