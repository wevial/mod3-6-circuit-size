"""mac_recheck.py (2026-10-25): re-solve every CNF that `CnfRuns.mod3_6_size_13`'s 22 hypotheses name,
on the Mac, and check every proof with two verified checkers.

Run on the Mac in ~/work (python3 >= 3.9, no deps), from a copy at ~/work/run/mac_recheck.py:

    python3 run/mac_recheck.py prepare          # export each split run's bases with the pinned cnfexport
    python3 run/mac_recheck.py pins             # sha256 of every binary and input; must equal run/pins.txt
    python3 run/mac_recheck.py controls         # runtime controls: both checkers must reject
    python3 run/mac_recheck.py probe leaf full6_12 10397 2048,4096,8192   # cake_lpr heap vs time, RSS
    nohup caffeinate -i nice python3 run/mac_recheck.py run --workers N [--scans-only] >> driver.log 2>&1 < /dev/null &
    python3 run/mac_recheck.py summary          # counts, times and peak RSS from results.tsv

For each CNF, Lean's `cnfexport` writes the DIMACS: a scan's with `cnfexport scan`, a leaf's as header +
base body + cube lines from `cnfexport leaves` (the bytes cnf_certify.py hashes). A leaf's sha256 must
equal that of a ledger line marked `UNSAT certified` at its index with the same cube; a scan's is compared
with the sha256 cnf_certify.out recorded. CaDiCaL 3.0.1 solves it with a binary LRAT proof to a file
(exit 20). Then two checkers read that proof:

* cake_lpr (CakeML, verified down to machine code, its DIMACS parser included) against the DIMACS file.
  It exits 0 on failure too, so the verdict is its stdout, which must be exactly `s VERIFIED UNSAT\n`.
* lratdirect (Lean, `Garden/LratDirect.lean`, `check_sound`) against the CNF it builds in memory from
  `CnfSpecs` (`lratdirect scan|leaf <run> <r|i> <proof>`): exit 0 and `s VERIFIED UNSAT (<label>: ...`.

The proof is deleted after both checks. CNF OK = sha256 matches, CaDiCaL exits 20, both checkers accept.

Resumable: results.tsv is append-only, one line per CNF; `run` skips CNFs that have an OK line, and will
not start if a file in pins.txt has changed or an earlier session ran under other pins. While
~/work/PAUSE exists no CNF starts, and the driver exits once the running ones finish. A FAIL line also
stops new starts, and is copied to ~/work/FAILED.

Order: scans first, then leaves by the ledger's solve+check seconds, hardest first. Memory: a worker
runs its three processes one after another, so its peak is the largest of theirs. cake_lpr's RSS is its
heap (CakeML's GC touches all of it), so the heap is fixed at CAKE_HEAP_MB, twice the smallest that
passed on the hardest leaf; WORKER_PEAK_MIB bounds a worker and N * WORKER_PEAK_MIB must fit MEM_BUDGET.
A CNF whose process exceeds WORKER_PEAK_MIB stops new starts, like PAUSE. A CNF starts only if the free
disk left after every running proof is written stays above DISK_FLOOR.
"""
import ast, calendar, hashlib, os, re, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

W = os.environ.get('RECHECK_HOME') or os.path.expanduser('~/work')     # RECHECK_HOME: for tests
BIN = os.path.join(W, 'lean-direct/direct/.lake/build/bin')
CADICAL = os.path.join(W, 'src/cadical/build/cadical')
CAKE = os.path.join(W, 'src/cake_lpr/cake_lpr')
EXPORT, DIRECT = os.path.join(BIN, 'cnfexport'), os.path.join(BIN, 'lratdirect')
LEDGERS = os.path.join(W, 'ledgers')           # copies of research/circuits/ledger_*.txt and cnf_certify.out
BASES = os.path.join(W, 'bases-direct')
PINS = os.path.join(W, 'run/pins.txt')
RESULTS = os.path.join(W, 'results.tsv')
TMP = os.path.join(W, 'tmp.noindex')         # .noindex: Spotlight skips it
PAUSE, FAILED = os.path.join(W, 'PAUSE'), os.path.join(W, 'FAILED')
# probe of the hardest leaf (full6_12 10397, 2.23 GB proof; tests/probe-10397.out): cake_lpr verified it at
# CML_HEAP_SIZE 1024/2048/4096/8192 in 69/60/59/56 s with peak RSS 1029/2053/4101/8197 MiB; lratdirect
# 247 s, 624 MiB; CaDiCaL 432 s, 318 MiB.
CAKE_HEAP_MB, CAKE_STACK_MB = 2048, 4096
WORKER_PEAK_MIB = 2100
CAKE_ENV = dict(os.environ, CML_HEAP_SIZE=str(CAKE_HEAP_MB), CML_STACK_SIZE=str(CAKE_STACK_MB))
MEM_BUDGET = 28 * 10**9                          # bytes, for all workers together
DISK_FLOOR = 55 * 10**9                          # 50 GB, plus margin
MAX_WORKERS = 12

LEDGER = {   # split run (cnfexport name) -> ledger file for (tag, depth); as cnf_certify.py
    'cube5_0': lambda tag, s: 'ledger_mod3_5_0_9_s2.txt',
    'cube5_2': lambda tag, s: 'ledger_mod3_5_2_9_s2.txt',
    'w2cube_8': lambda tag, s: 'ledger_w2_5_1_8_w2_s1.txt',
    'w2cube_9': lambda tag, s: 'ledger_w2_5_1_9_w2_s1.txt',
    'full6_12': lambda tag, s: 'ledger_mod3_6_1_12_s%d_elim2_sem12%s.txt' % (s, ['_x', '_x_S', '_x_S_E'][tag]),
}
COLUMNS = ['kind', 'run', 'i', 'record', 'sha256', 'sha', 'cadical', 'solve_s', 'solve_cpu', 'solve_MiB',
           'proof_MB', 'cake', 'cake_s', 'cake_cpu', 'cake_MiB', 'lratdirect', 'direct_s', 'direct_cpu',
           'direct_MiB', 'recorded_s', 'start', 'end', 'verdict']


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
    """Run cmd (stderr to a file in d); return (exit code, stdout bytes, stderr tail, wall s, cpu s,
    peak RSS MiB). CPU time and peak RSS come from wait4 on that process alone."""
    err = os.path.join(d, 'stderr')
    t0 = time.time()
    with open(err, 'wb') as e:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=e, stdin=subprocess.DEVNULL, env=env)
        out = p.stdout.read()
        _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    p.stdout.close()
    tail = open(err, 'rb').read()[-300:].decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rss = ru.ru_maxrss / (2**20 if sys.platform == 'darwin' else 2**10)
    return p.returncode, out, tail, time.time() - t0, ru.ru_utime + ru.ru_stime, rss


def cake_verdict(code, out, tail):
    ok = out == b's VERIFIED UNSAT\n'
    text = out.decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    return ok, (text if ok else 'REJECTED exit %d: %s' % (code, (text or tail)[:200] or '(no output)'))


def direct_verdict(code, out, tail, label):
    text = out.decode(errors='replace').strip().replace('\t', ' ')
    ok = code == 0 and text.startswith('s VERIFIED UNSAT (%s: ' % label) and '\n' not in text
    if ok:
        m = re.search(r'(\d+) actions', text)
        return True, 's VERIFIED UNSAT (%s actions)' % (m.group(1) if m else '?')
    return False, 'REJECTED exit %d: %s' % (code, (text.replace('\n', ' | ') or tail)[:300] or '(no output)')


# ---------------------------------------------------------------- jobs

def hypotheses():
    """The theorem's 22 hypotheses as Lean lists them: scans (name, lo, hi), splits (name, r, count)."""
    out = subprocess.run([EXPORT, 'list'], capture_output=True, text=True, check=True).stdout
    scans, splits = [], []
    for line in out.splitlines():
        kind, name, a, b = line.split('\t')
        (scans if kind == 'scan' else splits).append((name, int(a), int(b)))
    assert len(scans) + len(splits) == 22 and sorted(n for n, _, _ in splits) == sorted(LEDGER), out
    return scans, splits


def ledger(path):
    """idx -> [(sha256, recorded solve+check s)] for every line `UNSAT certified` with lratcheck's verdict,
    with that line's cube literals."""
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
    for line in open(os.path.join(LEDGERS, 'cnf_certify.out')):
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
        with open(os.path.join(d, 'manifest.tsv'), 'w') as f:
            f.write(man)
        print(name, count, 'leaves exported', flush=True)


def jobs():
    """Every CNF, in run order: scans as cnfexport lists them, then leaves hardest first. Each job is a
    dict with key (kind, run, i), the label lratdirect prints, and what its line is compared with."""
    scans, splits = hypotheses()
    rec = recorded_scans()
    out = []
    for name, lo, hi in scans:
        for r in range(lo, hi + 1):
            sha, secs = rec[name, r]
            out.append(dict(kind='scan', run=name, i=r, label='scan %s r=%d' % (name, r), want={sha},
                            record='cnf_certify.out', rec=secs))
    leaves, ledgers = [], {}
    for name, _, count in splits:
        rows = open(os.path.join(BASES, name, 'manifest.tsv')).read().splitlines()
        assert len(rows) == count, name
        for n, row in enumerate(rows):
            pos, tag, split, idx, hdr, cube = row.split('\t')
            pos, tag, split, idx = int(pos), int(tag), int(split), int(idx)
            assert pos == n, 'manifest out of order'
            lf = LEDGER[name](tag, split)
            if lf not in ledgers:
                ledgers[lf] = ledger(lf)
            lits = [int(c.split()[0]) for c in cube.split('|') if c]
            hits = [(sha, secs) for sha, secs, cb in ledgers[lf].get(idx, []) if cb == lits]
            leaves.append(dict(kind='leaf', run=name, i=pos, tag=tag, label='leaf %s %d' % (name, pos),
                               hdr=hdr, cube=cube, want={s for s, _ in hits}, record='%s:%d' % (lf, idx),
                               rec=max([t for _, t in hits] or [0.0])))
    leaves.sort(key=lambda j: (-j['rec'], j['run'], j['i']))
    return out + leaves


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
    key = (j['kind'], j['run'], j['i'])
    d = tempfile.mkdtemp(dir=TMP, prefix='job-')
    t0 = time.time()
    try:
        cnf, proof = os.path.join(d, 'f.cnf'), os.path.join(d, 'proof.lrat')
        RUNNING[key] = proof
        write_cnf(j, cnf)
        h = sha256(cnf)
        sha_ok = h in j['want']
        c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof], d)
        size = os.path.getsize(proof) if os.path.exists(proof) else 0
        none = (False, 'not run', 0.0, 0.0, 0.0)
        cake = direct = none
        if sha_ok and c[0] == 20:
            k = proc([CAKE, cnf, proof], d, CAKE_ENV)
            cake = cake_verdict(k[0], k[1], k[2]) + k[3:]
            x = proc([DIRECT] + direct_args(j) + [proof], d)
            direct = direct_verdict(x[0], x[1], x[2], j['label']) + x[3:]
        ok = sha_ok and c[0] == 20 and cake[0] and direct[0]
        f = [j['kind'], j['run'], j['i'], j['record'], h,
             ('= ' + ('ledger' if j['kind'] == 'leaf' else 'cnf_certify.out')) if sha_ok else 'MISMATCH',
             'exit %d' % c[0] if c[0] == 20 else 'exit %d: %s' % (c[0], c[2][:200]),
             '%.1f' % c[3], '%.1f' % c[4], '%.0f' % c[5], '%.1f' % (size / 1e6),
             cake[1], '%.1f' % cake[2], '%.1f' % cake[3], '%.0f' % cake[4],
             direct[1], '%.1f' % direct[2], '%.1f' % direct[3], '%.0f' % direct[4],
             '%.1f' % j['rec'], utc(t0), utc(time.time()), 'OK' if ok else 'FAIL']
        return f
    finally:
        RUNNING.pop(key, None)
        shutil.rmtree(d, ignore_errors=True)


# ---------------------------------------------------------------- pins

TOOLCHAIN = os.path.join(W, 'tools/lean-4.33.1-darwin_aarch64')


def pinned_files():
    """The binaries, the toolchain that built lratdirect and cnfexport, the Lean sources (with
    lean-direct/SOURCE naming their garden commit), the cake_lpr sources, this script, the ledgers and
    the exported bases."""
    files = [CADICAL, CAKE, DIRECT, EXPORT, os.path.abspath(__file__)]
    files += [os.path.join(TOOLCHAIN, 'bin', b) for b in ('lean', 'lake', 'leanc', 'clang', 'ld64.lld')]
    src = os.path.dirname(os.path.dirname(os.path.dirname(BIN)))      # lean-direct/
    for root, dirs, names in os.walk(src):
        dirs[:] = sorted(x for x in dirs if x != '.lake')
        files += sorted(os.path.join(root, f) for f in names)
    files += [os.path.join(os.path.dirname(CAKE), f) for f in ('basis_ffi.c', 'cake_lpr_arm8.S')]
    files += sorted(os.path.join(LEDGERS, f) for f in os.listdir(LEDGERS))
    for run in sorted(os.listdir(BASES)):
        files += sorted(os.path.join(BASES, run, f) for f in os.listdir(os.path.join(BASES, run)))
    return files


def sh(cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True).stdout.strip().replace('\n', ' ')
    except OSError:
        return '?'


def pins_text():
    """Comment lines (provenance, not checked) and one `sha256  path` line per pinned file."""
    head = ['# machine: %s, %s, %s bytes RAM, macOS %s (%s)' % (
                sh(['sysctl', '-n', 'hw.model']), sh(['sysctl', '-n', 'machdep.cpu.brand_string']),
                sh(['sysctl', '-n', 'hw.memsize']), sh(['sw_vers', '-productVersion']), sh(['sw_vers', '-buildVersion'])),
            '# cadical: git %s %s' % (sh(['git', '-C', os.path.join(W, 'src/cadical'), 'rev-parse', 'HEAD']),
                                      sh(['git', '-C', os.path.join(W, 'src/cadical'), 'describe', '--tags'])),
            '# cake_lpr: git %s; built `gcc basis_ffi.c cake_lpr_arm8.S -o cake_lpr -std=c99` (%s); '
            'run with CML_HEAP_SIZE=%d CML_STACK_SIZE=%d' % (
                sh(['git', '-C', os.path.dirname(CAKE), 'rev-parse', 'HEAD']), sh(['gcc', '--version']).split(' Target')[0],
                CAKE_HEAP_MB, CAKE_STACK_MB)]
    return ''.join(l + '\n' for l in head) + \
        ''.join('%s  %s\n' % (sha256(p), os.path.relpath(p, W)) for p in pinned_files())


def check_pins():
    """pins.txt's checksum lines must equal the files now; return the sha256 of pins.txt."""
    want = [l for l in open(PINS) if not l.startswith('#')]
    have = [l for l in pins_text().splitlines(True) if not l.startswith('#')]
    if want != have:
        bad = sorted(set(want) ^ set(have))
        raise SystemExit('pins.txt does not match the files:\n' + ''.join(bad[:20]))
    return sha256(PINS)


# ---------------------------------------------------------------- run

def done_keys(pins):
    """Keys with an OK line; refuses if an earlier session ran under other pins."""
    done = set()
    if not os.path.exists(RESULTS):
        return done
    for line in open(RESULTS):
        if line.startswith('# session'):
            m = re.search(r'pins ([0-9a-f]{64})', line)
            if not m or m.group(1) != pins:
                raise SystemExit('results.tsv has a session under other pins: ' + line)
        elif not line.startswith('#'):
            t = line.rstrip('\n').split('\t')
            if t[-1] == 'OK':
                done.add((t[0], t[1], int(t[2])))
    return done


def free_disk():
    s = os.statvfs(W)
    return s.f_bavail * s.f_frsize


def disk_ok(j, running):
    pending = 0.0
    for r in running:
        p = RUNNING.get((r['kind'], r['run'], r['i']))
        cur = os.path.getsize(p) if p and os.path.exists(p) else 0
        pending += max(0.0, est_proof_bytes(r['rec']) - cur)
    return free_disk() - pending - est_proof_bytes(j['rec']) >= DISK_FLOOR


def append(line):
    with open(RESULTS, 'a') as f:
        f.write(line + '\n')
        f.flush()
        os.fsync(f.fileno())


def run(workers, scans_only=False):
    assert 1 <= workers <= MAX_WORKERS and workers * WORKER_PEAK_MIB * 2**20 <= MEM_BUDGET, workers
    pins = check_pins()
    for d in os.listdir(TMP):                      # a killed session's temp dirs
        if d.startswith('job-'):
            shutil.rmtree(os.path.join(TMP, d), ignore_errors=True)
    if os.path.exists(FAILED):
        raise SystemExit('~/work/FAILED exists: look at it before running again')
    done = done_keys(pins)
    todo = [j for j in jobs() if (j['kind'], j['run'], j['i']) not in done and (j['kind'] == 'scan' or not scans_only)]
    if not os.path.exists(RESULTS):
        append('# ' + '\t'.join(COLUMNS))
    append('# session %s pid %d pins %s workers %d mem_budget %d disk_floor %d: %d done, %d to do'
           % (utc(time.time()), os.getpid(), pins, workers, MEM_BUDGET, DISK_FLOOR, len(done), len(todo)))
    print('%s: %d done, %d to do, %d workers' % (utc(time.time()), len(done), len(todo), workers), flush=True)
    running, stop, nfail = {}, None, 0
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
                append(line)
                if f[-1] != 'OK':
                    nfail += 1
                    with open(FAILED, 'a') as g:
                        g.write(line + '\n')
                elif stop is None and max(float(f[i]) for i in (9, 14, 18)) > WORKER_PEAK_MIB:
                    stop = 'a process of %s %s %s exceeded WORKER_PEAK_MIB' % tuple(f[:3])
            if stop is None and os.path.exists(FAILED):
                stop = 'a CNF failed (see FAILED)'
            if stop is None and os.path.exists(PAUSE):
                stop = 'PAUSE'
            if stop is not None:
                if not running:
                    break
            else:
                while todo and len(running) < workers:
                    j = todo[0]
                    rs = list(running.values())
                    if not disk_ok(j, rs):
                        if not rs:
                            stop = 'disk below the floor with nothing running'
                        break
                    todo.pop(0)
                    running[ex.submit(run_job, j)] = j
            time.sleep(2)
    why = stop or ('all scans done' if scans_only else 'all done')
    append('# end %s: %s; %d left; %d failed this session' % (utc(time.time()), why, len(todo), nfail))
    print('%s: stopped: %s; %d left, %d failed' % (utc(time.time()), why, len(todo), nfail), flush=True)
    sys.exit(1 if nfail else 2 if todo else 0)       # 0: all done; 1: a CNF failed; 2: stopped early


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
    """Both checkers must reject a proof with one bit flipped and a proof for a different CNF. Each
    base proof must first be accepted by both."""
    check_pins()
    allok = True
    by = {(j['kind'], j['run'], j['i']): j for j in jobs()}
    cases = [(by['scan', 'best4_0', 6], by['scan', 'best4_1', 6])]
    lv = sorted((j for j in by.values() if j['kind'] == 'leaf' and j['run'] == 'full6_12'
                 and 60 <= j['rec'] <= 120), key=lambda j: j['i'])
    a = lv[len(lv) // 2]
    cases.append((a, by['leaf', 'full6_12', a['i'] + 1]))
    for a, b in cases:
        d = tempfile.mkdtemp(dir=TMP, prefix='ctl-')
        try:
            fa, fb, proof, g = (os.path.join(d, x) for x in ('a.cnf', 'b.cnf', 'proof.lrat', 'flip.lrat'))
            write_cnf(a, fa)
            write_cnf(b, fb)
            c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', fa, proof], d)
            base_cake = cake_verdict(*proc([CAKE, fa, proof], d, CAKE_ENV)[:3])
            base_direct = direct_verdict(*proc([DIRECT] + direct_args(a) + [proof], d)[:3], a['label'])
            ok = c[0] == 20 and base_cake[0] and base_direct[0] and sha256(fa) in a['want'] \
                and sha256(fb) in b['want']
            print('base: %s (sha256 %s): cadical exit %d; cake_lpr %s; lratdirect %s -> %s'
                  % (a['label'], 'matches' if sha256(fa) in a['want'] else 'MISMATCH', c[0], base_cake[1],
                     base_direct[1], 'accepted' if ok else 'NOT ACCEPTED'), flush=True)
            allok &= ok
            k = cake_verdict(*proc([CAKE, fb, proof], d, CAKE_ENV)[:3])
            x = direct_verdict(*proc([DIRECT] + direct_args(b) + [proof], d)[:3], b['label'])
            good = not k[0] and not x[0]
            print('  (1) proof of %s given as %s: cake_lpr %s; lratdirect %s -> %s'
                  % (a['label'], b['label'], k[1], x[1], 'both rejected' if good else 'NOT BOTH REJECTED'),
                  flush=True)
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
                good = not k[0] and not x[0]
                print('  (2) %s proof, bit %d of byte %d of %d flipped (%s): cake_lpr %s; lratdirect %s -> %s'
                      % (a['label'], bit, pos, n, what, k[1], x[1], 'both rejected' if good else 'NOT BOTH REJECTED'),
                      flush=True)
                allok &= good
        finally:
            shutil.rmtree(d, ignore_errors=True)
    print('CONTROLS %s' % ('PASSED: every base proof accepted by both, every altered one rejected by both'
                           if allok else 'FAILED'), flush=True)
    sys.exit(0 if allok else 1)


# ---------------------------------------------------------------- summary

def summary():
    rows, sessions = [], []
    if not os.path.exists(RESULTS):
        raise SystemExit('no results.tsv yet')
    for line in open(RESULTS):
        if line.startswith('# session') or line.startswith('# end'):
            sessions.append(line.strip())
        elif not line.startswith('#'):
            rows.append(dict(zip(COLUMNS, line.rstrip('\n').split('\t'))))
    want = {(j['kind'], j['run'], j['i']) for j in jobs()}
    ok = {(r['kind'], r['run'], int(r['i'])) for r in rows if r['verdict'] == 'OK'}
    fails = [r for r in rows if r['verdict'] != 'OK']
    print('# summary %s' % utc(time.time()))
    for kind in ('scan', 'leaf'):
        w = {k for k in want if k[0] == kind}
        print('%s: %d/%d CNFs OK (sha256 matched, CaDiCaL exit 20, cake_lpr `s VERIFIED UNSAT`, lratdirect '
              '`s VERIFIED UNSAT`)' % (kind, len(w & ok), len(w)))
        for run in sorted({k[1] for k in w}):
            wr = {k for k in w if k[1] == run}
            print('  %s: %d/%d' % (run, len(wr & ok), len(wr)))
    print('FAIL lines: %d' % len(fails))
    for r in fails:
        later = (r['kind'], r['run'], int(r['i'])) in ok
        print('  ' + '\t'.join(r.get(c, '') for c in COLUMNS) + ('\t(an OK line for this CNF follows)' if later else ''))
    good = [r for r in rows if r['verdict'] == 'OK']
    f = lambda c: sum(float(r[c]) for r in good)
    print('times over OK lines, hours: solve %.1f wall / %.1f CPU; cake_lpr %.1f / %.1f; lratdirect %.1f / %.1f; '
          'ledger solve+check %.1f' % (f('solve_s') / 3600, f('solve_cpu') / 3600, f('cake_s') / 3600,
                                       f('cake_cpu') / 3600, f('direct_s') / 3600, f('direct_cpu') / 3600,
                                       f('recorded_s') / 3600))
    print('proofs written and deleted: %.1f GB' % (f('proof_MB') / 1e3))
    for c, name in (('solve_MiB', 'CaDiCaL'), ('cake_MiB', 'cake_lpr'), ('direct_MiB', 'lratdirect')):
        if not good:
            break
        m = max(good, key=lambda r: float(r[c]))
        print('peak RSS, %s: %s MiB (%s %s %s)' % (name, m[c], m['kind'], m['run'], m['i']))
    ev = []
    for r in good:
        peak = max(float(r['solve_MiB']), float(r['cake_MiB']), float(r['direct_MiB']))
        t0 = calendar.timegm(time.strptime(r['start'], '%Y-%m-%dT%H:%M:%SZ'))
        t1 = calendar.timegm(time.strptime(r['end'], '%Y-%m-%dT%H:%M:%SZ'))
        ev += [(t0, 1, peak), (t1 + 1, -1, peak)]
    cur = top = 0.0
    for _, s, p in sorted(ev, key=lambda e: (e[0], e[1])):
        cur += s * p
        top = max(top, cur)
    print('bound on concurrent RSS (sum of the peaks of CNFs whose runs overlap): %.1f GiB' % (top / 1024))
    print('sessions:')
    for s in sessions:
        print('  ' + s)


def probe(kind, run_, i, heaps):
    """Solve one CNF once, keep its proof, and check it with cake_lpr at each CML_HEAP_SIZE (MB) in
    heaps and with lratdirect once: the time and peak RSS behind CAKE_HEAP_MB and WORKER_PEAK_MIB."""
    j = {(x['kind'], x['run'], x['i']): x for x in jobs()}[kind, run_, i]
    d = tempfile.mkdtemp(dir=TMP, prefix='probe-')
    try:
        cnf, proof = os.path.join(d, 'f.cnf'), os.path.join(d, 'proof.lrat')
        write_cnf(j, cnf)
        print('%s: sha256 %s; ledger solve+check %.1fs' % (j['label'], 'matches' if sha256(cnf) in j['want']
                                                           else 'MISMATCH', j['rec']), flush=True)
        c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof], d)
        print('  cadical exit %d [%.1fs wall, %.1fs CPU, %.0f MiB]; proof %.1f MB'
              % (c[0], c[3], c[4], c[5], os.path.getsize(proof) / 1e6), flush=True)
        for h in heaps:
            k = proc([CAKE, cnf, proof], d, dict(os.environ, CML_HEAP_SIZE=str(h), CML_STACK_SIZE=str(CAKE_STACK_MB)))
            print('  cake_lpr CML_HEAP_SIZE=%d: %s [%.1fs wall, %.1fs CPU, %.0f MiB]'
                  % (h, cake_verdict(k[0], k[1], k[2])[1], k[3], k[4], k[5]), flush=True)
        x = proc([DIRECT] + direct_args(j) + [proof], d)
        print('  lratdirect: %s [%.1fs wall, %.1fs CPU, %.0f MiB]'
              % (direct_verdict(x[0], x[1], x[2], j['label'])[1], x[3], x[4], x[5]), flush=True)
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main():
    a = sys.argv[1:]
    os.makedirs(TMP, exist_ok=True)
    if a == ['prepare']:
        prepare()
    elif a == ['pins']:
        sys.stdout.write(pins_text())
    elif a == ['controls']:
        controls()
    elif a[:1] == ['probe'] and len(a) == 5:
        probe(a[1], a[2], int(a[3]), [int(h) for h in a[4].split(',')])
    elif a[:1] == ['run']:
        run(int(a[a.index('--workers') + 1]) if '--workers' in a else 1, '--scans-only' in a)
    elif a == ['summary']:
        summary()
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
