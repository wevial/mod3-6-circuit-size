"""direct_check.py (2026-10-25): re-solve the scan CNFs and a random 1% of the leaves, and check each
proof two ways: against the CNF built in memory (`lratdirect`) and against the exported DIMACS
(`lratcheck`).

Usage (after `cd ../lean && lake build cnfexport lratcheck lratdirect`; no Python deps):

    REV=$(git rev-parse HEAD) TMPDIR=<fresh dir> python3 direct_check.py > direct_check.out
    python3 direct_check.py --plan                       # the sample and its ledger times; solves nothing
    python3 direct_check.py --leaves full6_12:17,...      # only these leaves (timing); no scans

`lratdirect scan|leaf <run> <r|i> <proof>` builds the CNF that `CnfRuns.mod3_6_size_13`'s hypothesis
names (`toCNF (R.cnf r)`, `toCNF ((R L.tag).leafCnf r L.cube)`, looked up in `CnfSpecs.scanList` /
`splitList`) in memory and reads only the proof: no DIMACS writer, parser or sha256 link between the
Lean CNF and the verdict (`Garden/LratDirect.lean`, `check_sound`, `scan_sound`, `leaf_sound`).

For every job below: `cnfexport` writes the DIMACS, CaDiCaL solves it with a binary LRAT proof to a temp
file (exit 20), then `lratdirect` and `lratcheck` each check that proof (exit 0 and `s VERIFIED UNSAT`).

* Scans: all 92 CNFs (every r of every scan in `cnfexport list`). The DIMACS sha256 must also equal the
  digest `cnf_certify.out` recorded for it.
* Leaves: a random 1% (rounded up: 134) of the 13,347 leaves of the 5 split runs, in `splitList` order.
  The seed is the sha256 of the main commit this session started from (SEED_COMMIT below, fixed before
  any leaf was solved). For each, the whole-leaf export (`cnfexport leaf`) must have the sha256 of a
  ledger line marked `UNSAT certified` with `lratcheck`'s verdict, at that leaf's index, with the same
  cube literals.
* Runtime controls, first: `lratdirect` must reject (1) a proof of another CNF (best4_0 r=6's proof as
  best4_1 r=6, and the first sampled r = 12 leaf's proof as its neighbour leaf) and (2) a proof with one
  byte flipped (bit 0 of the byte at 1/4, 1/2, 3/4 and at the last hint of best4_0 r=6's proof; the
  middle byte of that leaf's proof). The leaf controls run on the sampled leaf's own proof, inside the
  sample. Also: best4_0 r=6 solved again with a text LRAT proof, which lratdirect must accept.

The controls are empirical: a proof that does not use the changed clause, or a flip in an unused hint or
an irrelevant deletion, could still be valid, so `NOT REJECTED` would need a look before calling it a
checker defect. Each process's CPU time and peak RSS come from `os.wait4`. Temp files go in a fresh
directory under TMPDIR, deleted as each job finishes and on any exit.
"""
import ast, hashlib, math, os, random, re, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

import cnf_certify as cc

HERE = cc.HERE
# Paths can be overridden (e.g. on a machine without the garden's /cache): CNFEXPORT, LRATDIRECT,
# LRATCHECK, CADICAL.
EXPORT = cc.EXPORT = os.environ.get('CNFEXPORT', cc.EXPORT)
CHECK = os.environ.get('LRATCHECK', cc.CHECK)
CADICAL = os.environ.get('CADICAL', cc.CADICAL)
DIRECT = os.environ.get('LRATDIRECT', os.path.join(cc.LEAN, 'lratdirect'))
SEED_COMMIT = '6ff39376ab06fa32d2fe56ff345d5fcc49f61ad3'   # origin/main when this session started
FRACTION = 0.01
WORKERS = int(os.environ.get('WORKERS', '3'))


def proc(cmd):
    """Run cmd; return (exit code, output, wall s, cpu s, peak RSS MiB)."""
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    p.stdout.close()
    rss = ru.ru_maxrss / (1024 * 1024 if sys.platform == 'darwin' else 1024)
    return p.returncode, out.strip(), time.time() - t0, ru.ru_utime + ru.ru_stime, rss


def verdict(out):
    m = re.search(r'^s (VERIFIED UNSAT|NOT VERIFIED).*$', out, re.M)
    return m.group(0) if m else out.splitlines()[-1] if out else '(no output)'


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def solve_and_check(cnf, direct_args, d):
    """CaDiCaL -> proof file; then lratdirect and lratcheck on it. Returns (ok, text, cpu s)."""
    proof = os.path.join(d, 'proof.lrat')
    c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof])
    size = os.path.getsize(proof) if os.path.exists(proof) else 0
    x = proc([DIRECT, *direct_args, proof])
    k = proc([CHECK, cnf, proof])
    ok = (c[0] == 20 and x[0] == 0 and verdict(x[1]).startswith('s VERIFIED UNSAT')
          and k[0] == 0 and verdict(k[1]).startswith('s VERIFIED UNSAT'))
    text = (f'cadical exit {c[0]} [{c[2]:.1f}s, {size / 1e6:.1f} MB proof, {c[4]:.0f} MiB]; '
            f'lratdirect exit {x[0]}: {verdict(x[1])} [{x[2]:.1f}s, {x[4]:.0f} MiB]; '
            f'lratcheck exit {k[0]}: {verdict(k[1])} [{k[2]:.1f}s, {k[4]:.0f} MiB]')
    return ok, text, c[3] + x[3] + k[3], proof


def recorded_scans():
    """(name, r) -> the full sha256 cnf_certify.out recorded for that scan CNF."""
    out = {}
    for line in open(os.path.join(HERE, 'cnf_certify.out')):
        m = re.match(r'\s+(\S+) r=(\d+): sha256 ([0-9a-f]{64}) ', line)
        if m:
            out[m.group(1), int(m.group(2))] = m.group(3)
    return out


def all_leaves(splits, tmp):
    """Every leaf of every split run, in splitList order: (run, i, tag, split, idx, cube lits)."""
    leaves = []
    for name, _, count in splits:
        d = tempfile.mkdtemp(dir=tmp)
        man = subprocess.run([EXPORT, 'leaves', name, d], capture_output=True, text=True, check=True).stdout
        shutil.rmtree(d, ignore_errors=True)
        rows = [l.split('\t') for l in man.splitlines()]
        assert len(rows) == count and all(int(r[0]) == i for i, r in enumerate(rows)), name
        for r in rows:
            lits = [int(c.split()[0]) for c in r[5].split('|') if c]
            leaves.append((name, int(r[0]), int(r[1]), int(r[2]), int(r[3]), lits))
    return leaves


def sample(n):
    seed = int(hashlib.sha256(SEED_COMMIT.encode()).hexdigest(), 16)
    k = math.ceil(n * FRACTION)
    return seed, sorted(random.Random(seed).sample(range(n), k))


LEDGERS = {}


def ledger_lines(run, tag, split, idx):
    lf = cc.LEDGER[run](tag, split)
    if lf not in LEDGERS:
        LEDGERS[lf] = cc.ledger(lf)
    return lf, LEDGERS[lf].get(idx, [])


def ledger_time(leaf):
    """The ledger's solve+check seconds on the certified line for this leaf (FIFO, solver and lratcheck
    side by side)."""
    run, _, tag, split, idx, _ = leaf
    lf = cc.LEDGER[run](tag, split)
    for line in open(os.path.join(HERE, lf)):
        t = line.rstrip('\n').split('\t')
        if t[0] == str(idx) and t[2] == 'UNSAT' and t[3] == 'certified':
            return lf, float(re.search(r'=([0-9.]+)s', t[4]).group(1))
    return lf, float('nan')


def leaf_job(leaf, tmp, nleaves, with_controls=False):
    run, i, tag, split, idx, lits = leaf
    d = tempfile.mkdtemp(dir=tmp)
    f = os.path.join(d, 'leaf.cnf')
    subprocess.run([EXPORT, 'leaf', run, str(i), f], check=True)
    h = sha256(f)
    lf, lines = ledger_lines(run, tag, split, idx)
    match = any(st == 'UNSAT' and c == 'certified' and det.startswith('s VERIFIED UNSAT') and sha == h
                and ast.literal_eval(cb) == lits for st, c, sha, cb, det in lines)
    ok, text, cpu, proof = solve_and_check(f, ['leaf', run, str(i)], d)
    out = (f'  leaf {run} {i} (ledger {lf} idx {idx}): sha256 {h} '
           f'{"= a certified ledger line" if match else "MATCHES NO CERTIFIED LEDGER LINE"}; {text}')
    ctl = True
    if with_controls:       # on this leaf's own proof, so the controls cost no extra solve
        nb = i + 1 if i + 1 < nleaves else i - 1
        good, t = reject(['leaf', run, str(nb)], proof)
        out += (f'\n  control (1) leaf {run} {i}\'s proof as leaf {run} {nb}: lratdirect {t} -> '
                f'{"rejected" if good else "NOT REJECTED"}')
        ctl &= good
        n = os.path.getsize(proof)
        g = os.path.join(d, 'flip.lrat')
        flipped(proof, g, n // 2)
        good, t = reject(['leaf', run, str(i)], g)
        _, kout, _, _, _ = proc([CHECK, f, g])
        out += (f'\n  control (2) leaf {run} {i}\'s proof, byte {n // 2} of {n} (1/2) xor 1: lratdirect {t} -> '
                f'{"rejected" if good else "NOT REJECTED"} (lratcheck: {verdict(kout)})')
        ctl &= good
    shutil.rmtree(d, ignore_errors=True)
    return match and ok, ctl, cpu, out


def scan_job(job, tmp, rec):
    name, r = job
    d = tempfile.mkdtemp(dir=tmp)
    f = os.path.join(d, f'{name}_{r}.cnf')
    subprocess.run([EXPORT, 'scan', name, str(r), f], check=True)
    h = sha256(f)
    same = rec.get((name, r)) == h
    ok, text, cpu, _ = solve_and_check(f, ['scan', name, str(r)], d)
    shutil.rmtree(d, ignore_errors=True)
    return (ok, cpu, f'  scan {name} r={r}: sha256 {h} {"= cnf_certify.out" if same else "!= cnf_certify.out"}; '
                     f'{text}', same)


def flipped(src, dst, pos):
    data = bytearray(open(src, 'rb').read())
    data[pos] ^= 0x01
    open(dst, 'wb').write(data)


def reject(args, proof):
    code, out, wall, _, _ = proc([DIRECT, *args, proof])
    return code == 1 and verdict(out).startswith('s NOT VERIFIED'), f'exit {code}: {verdict(out)} [{wall:.1f}s]'


def controls(tmp):
    """Runtime controls on best4_0 r=6: lratdirect must reject another CNF's proof and one-byte flips,
    and accept the same proof in text LRAT (the format cake_lpr reads)."""
    allok = True
    d = tempfile.mkdtemp(dir=tmp)
    f = os.path.join(d, 'a.cnf')
    subprocess.run([EXPORT, 'scan', 'best4_0', '6', f], check=True)
    ok, text, _, proof = solve_and_check(f, ['scan', 'best4_0', '6'], d)
    print(f'  control base: scan best4_0 r=6: {text}', flush=True)
    allok &= ok
    good, t = reject(['scan', 'best4_1', '6'], proof)
    print(f'  control (1) best4_0 r=6\'s proof as scan best4_1 r=6: lratdirect {t} -> '
          f'{"rejected" if good else "NOT REJECTED"}', flush=True)
    allok &= good
    n = os.path.getsize(proof)
    for label, pos in [('1/4', n // 4), ('1/2', n // 2), ('3/4', 3 * n // 4), ('last hint of the empty clause', n - 2)]:
        g = os.path.join(d, 'flip.lrat')
        flipped(proof, g, pos)
        good, t = reject(['scan', 'best4_0', '6'], g)
        _, kout, _, _, _ = proc([CHECK, f, g])
        print(f'  control (2) best4_0 r=6\'s proof, byte {pos} of {n} ({label}) xor 1: lratdirect {t} -> '
              f'{"rejected" if good else "NOT REJECTED"} (lratcheck: {verdict(kout)})', flush=True)
        allok &= good
    tp = os.path.join(d, 'text.lrat')
    c = proc([CADICAL, '-q', '--lrat=true', '--binary=false', f, tp])
    x = proc([DIRECT, 'scan', 'best4_0', '6', tp])
    good = c[0] == 20 and x[0] == 0 and verdict(x[1]).startswith('s VERIFIED UNSAT')
    print(f'  control (text) best4_0 r=6, text LRAT ({os.path.getsize(tp) / 1e6:.1f} MB): cadical exit {c[0]}; '
          f'lratdirect exit {x[0]}: {verdict(x[1])} -> {"accepted" if good else "NOT ACCEPTED"}', flush=True)
    allok &= good
    shutil.rmtree(d, ignore_errors=True)
    return allok


def main():
    args = sys.argv[1:]
    plan = '--plan' in args
    only = None
    if '--leaves' in args:
        only = [(s.split(':')[0], int(s.split(':')[1])) for s in args[args.index('--leaves') + 1].split(',')]
    tmp = tempfile.mkdtemp(dir=os.environ.get('TMPDIR') or tempfile.gettempdir())
    try:
        run(args, plan, only, tmp)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def run(args, plan, only, tmp):
    t_all = time.time()
    print(f'# sources: git {os.environ.get("REV", "(set REV)")}; seed commit {SEED_COMMIT}', flush=True)
    scans, splits = cc.hypotheses()
    assert len(scans) + len(splits) == 22, 'hypothesis list'
    leaves = all_leaves(splits, tmp)
    seed, picks = sample(len(leaves))
    print(f'# seed = sha256("{SEED_COMMIT}") = {seed:x}', flush=True)
    print(f'# sample: random.Random(seed).sample(range({len(leaves)}), {len(picks)}), sorted: {picks}',
          flush=True)
    chosen = [leaves[p] for p in picks]
    if only is not None:
        pos = {(l[0], l[1]): l for l in leaves}
        chosen = [pos[x] for x in only]
    if plan:
        tot = 0.0
        for l in chosen:
            lf, t = ledger_time(l)
            tot += t
            print(f'  {l[0]} {l[1]}: {lf} idx {l[4]}, ledger solve+check {t:.1f}s')
        print(f'# ledger solve+check for these {len(chosen)} leaves: {tot:.0f}s = {tot / 3600:.2f} h')
        return
    allok = ctl_ok = True
    if only is None:
        print('controls:', flush=True)
        ctl_ok = controls(tmp)
    first12 = next((k for k, l in enumerate(chosen) if l[0] == 'full6_12'), None) if only is None else None
    count = {name: c for name, _, c in splits}
    nscan = nsame = 0
    cpu_scan = cpu_leaf = 0.0
    t0 = time.time()
    if only is None:
        rec = recorded_scans()
        jobs = [(name, r) for name, lo, hi in scans for r in range(lo, hi + 1)]
        print(f'scans ({len(jobs)} CNFs):', flush=True)
        with ThreadPoolExecutor(WORKERS) as ex:
            for ok, cpu, line, same in ex.map(lambda j: scan_job(j, tmp, rec), jobs):
                print(line, flush=True)
                allok &= ok and same      # verified by both, and the same CNF cnf_certify.out solved
                nscan += ok
                nsame += same
                cpu_scan += cpu
    t_scan = time.time() - t0
    t0 = time.time()
    nleaf = 0
    print(f'leaves ({len(chosen)}):', flush=True)
    with ThreadPoolExecutor(WORKERS) as ex:
        for ok, ctl, cpu, line in ex.map(lambda kl: leaf_job(kl[1], tmp, count[kl[1][0]], kl[0] == first12),
                                         enumerate(chosen)):
            print(line, flush=True)
            allok &= ok
            ctl_ok &= ctl
            nleaf += ok
            cpu_leaf += cpu
    t_leaf = time.time() - t0
    allok &= ctl_ok
    print(f'{"ALL VERIFIED" if allok else "NOT ALL VERIFIED"}: '
          + (f'controls {"all as required" if ctl_ok else "NOT ALL AS REQUIRED"}; {nscan}/{len(jobs)} scan CNFs verified by lratdirect and lratcheck '
             f'({nsame} with cnf_certify.out\'s sha256) [{t_scan:.0f}s wall, {cpu_scan:.0f}s CPU]; ' if only is None else '')
          + f'{nleaf}/{len(chosen)} leaves sha256-matched to their ledger lines and verified by lratdirect and '
            f'lratcheck [{t_leaf:.0f}s wall, {cpu_leaf:.0f}s CPU]; total {time.time() - t_all:.0f}s wall, '
            f'{WORKERS} workers', flush=True)
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
