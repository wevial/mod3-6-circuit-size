"""cnf_certify.py (2026-10-24): certify every CNF that Lean's `CnfRuns.mod3_6_size_13` names.

Usage:  REV=$(git rev-parse HEAD) TMPDIR=/scratch python3 cnf_certify.py [--resume <earlier output>]... \
            > cnf_certify.out      (after `cd ../lean && lake build cnfexport lratcheck`; ~12 min on one
                                    CPU without --resume; no Python deps)

The theorem's 22 hypotheses say that CNFs generated *in Lean* (Garden/CnfGen.lean, exported by the
`cnfexport` executable) are unsatisfiable. The list of them is read from Lean (`cnfexport list`, i.e.
`CnfSpecs.scanList` and `splitList`, which `CnfRuns.mod3_6_size_13_lists` takes as its hypotheses), so
the ranges and leaf lists checked here are the theorem's. Each is shown certified one of two ways:

* Split runs (n = 5 r = 9, w2_5^1 r = 8, 9, MOD3^1_6 r = 12): for every leaf, the Lean export is
  byte-identical to the DIMACS some ledger line certified: same sha256, line `UNSAT certified`, with
  `lratcheck`'s verdict `s VERIFIED UNSAT` (a CaDiCaL LRAT proof accepted by Lean's verified checker).
  The leaf's bytes are `cnfexport leaves`' header + base body + cube lines (`CnfRuns.dimacs_append`,
  `CnfRuns.leafCnf_split`); a few leaves per run are also exported whole (`cnfexport leaf`) and compared
  byte for byte, and the number of leaves must be the Lean list's. The 12-gate search is never rerun.
* Scans (every other run, every r): the Lean export is solved again here by CaDiCaL, its binary LRAT
  streamed through a FIFO into `lratcheck`, which must print `s VERIFIED UNSAT` and exit 0.

Also: every scan file and one leaf per split run go through `lratcheck --dump-cnf`, which must
reproduce the file byte for byte; and a positive control: Lean's r = 13 CNF for the cube that came
back SAT is that ledger line's DIMACS, and the model recorded there satisfies every clause.

`--resume <earlier output>` (repeatable): a scan CNF that an earlier output records as solved there
(or as reused there, with the digest the solving run recorded) is exported again; if its sha256
starts with the recorded digest (16 or 64 hex digits), the earlier verdict is reported instead of
solving again, with the recorded digest, so a reuse never strengthens the link. Split runs are always
re-hashed.
"""
import ast, hashlib, os, random, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '../lean/.lake/build/bin')
EXPORT, CHECK = os.path.join(LEAN, 'cnfexport'), os.path.join(LEAN, 'lratcheck')
CADICAL = '/cache/elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical'

LEDGER = {   # split run (cnfexport name) -> ledger file for (tag, depth)
    'cube5_0': lambda tag, s: 'ledger_mod3_5_0_9_s2.txt',
    'cube5_2': lambda tag, s: 'ledger_mod3_5_2_9_s2.txt',
    'w2cube_8': lambda tag, s: 'ledger_w2_5_1_8_w2_s1.txt',
    'w2cube_9': lambda tag, s: 'ledger_w2_5_1_9_w2_s1.txt',
    'full6_12': lambda tag, s: f'ledger_mod3_6_1_12_s{s}_elim2_sem12{["_x", "_x_S", "_x_S_E"][tag]}.txt',
}


def hypotheses():
    """The theorem's 22 hypotheses, as Lean lists them (`CnfSpecs.scanList`, `splitList`):
    scans (name, lo, hi) and split runs (name, r, leaf count)."""
    out = subprocess.run([EXPORT, 'list'], capture_output=True, text=True, check=True).stdout
    scans, splits = [], []
    for line in out.splitlines():
        kind, name, a, b = line.split('\t')
        (scans if kind == 'scan' else splits).append((name, int(a), int(b)))
    return scans, splits


def ledger(path):
    """idx -> list of (status, certified, sha, cube, checker's line) for every line."""
    out = {}
    for line in open(os.path.join(HERE, path)):
        t = line.rstrip('\n').split('\t')
        out.setdefault(int(t[0]), []).append((t[2], t[3], t[6], t[1], t[5]))
    return out


def dump_roundtrip(path):
    p = subprocess.run([CHECK, '--dump-cnf', path], capture_output=True, check=True)
    return p.stdout == open(path, 'rb').read()


def split_run(name, nleaves, tmp):
    ledger_of = LEDGER[name]
    t0 = time.time()
    d = tempfile.mkdtemp(dir=tmp)
    man = subprocess.run([EXPORT, 'leaves', name, d], capture_output=True, text=True, check=True).stdout
    bodies, ledgers, mids = {}, {}, {}
    ok = bad = 0
    leaves = []
    for line in man.splitlines():
        pos, tag, split, idx, hdr, cube = line.split('\t')
        pos, tag, split, idx = int(pos), int(tag), int(split), int(idx)
        assert pos == len(leaves), 'manifest out of order'
        if tag not in bodies:
            bodies[tag] = open(os.path.join(d, f'base{tag}.body'), 'rb').read()
        lf = ledger_of(tag, split)
        if lf not in ledgers:
            ledgers[lf] = ledger(lf)
        tail = cube.replace('|', '\n').encode()
        if (tag, hdr) not in mids:          # sha256 midstate after header + base body
            mids[tag, hdr] = hashlib.sha256(hdr.encode() + b'\n' + bodies[tag])
        m = mids[tag, hdr].copy()
        m.update(tail)
        h = m.hexdigest()
        lits = [int(c.split()[0]) for c in cube.split('|') if c]
        lines = ledgers[lf].get(idx, [])
        good = any(st == 'UNSAT' and c == 'certified' and det.startswith('s VERIFIED UNSAT') and sha == h
                   for st, c, sha, _, det in lines)     # lratcheck's verdict, on these exact bytes
        if good and all(ast.literal_eval(cb) == lits for _, _, _, cb, _ in lines):
            ok += 1
        else:
            bad += 1
            print(f'  MISMATCH {name} tag={tag} split={split} idx={idx} ({lf}): lean sha {h[:16]}, '
                  f'ledger {[(st, c, sha[:16]) for st, c, sha, _, _ in lines]}', flush=True)
        leaves.append((hdr, tag, tail))
    # spot checks: the fast path against the whole export, and lratcheck's parser
    random.seed(20261024)
    picks = sorted({0, len(leaves) - 1, *random.sample(range(len(leaves)), min(3, len(leaves)))})
    spot = 0
    for i in picks:
        f = os.path.join(d, 'leaf.cnf')
        subprocess.run([EXPORT, 'leaf', name, str(i), f], check=True)
        hdr, tag, tail = leaves[i]
        spot += open(f, 'rb').read() == hdr.encode() + b'\n' + bodies[tag] + tail
        if i == picks[0]:
            rt = dump_roundtrip(f)
    shutil.rmtree(d, ignore_errors=True)
    print(f'{name}: {ok}/{len(leaves)} leaves byte-identical to a certified ledger line (sha256), '
          f'{bad} mismatches; whole-leaf export = header+body+cube for {spot}/{len(picks)} sampled; '
          f'--dump-cnf round-trip {"identical" if rt else "DIFFERS"} [{time.time() - t0:.1f}s]', flush=True)
    complete = len(leaves) == nleaves and nleaves > 0
    if not complete:
        print(f'  INCOMPLETE {name}: {len(leaves)} leaves exported, {nleaves} in the Lean list', flush=True)
    return bad == 0 and spot == len(picks) and rt and complete, len(leaves)


def solve(path, tmp):
    d = tempfile.mkdtemp(dir=tmp)
    fifo = os.path.join(d, 'proof.fifo')
    os.mkfifo(fifo)
    t0 = time.time()
    chk = subprocess.Popen([CHECK, path, fifo], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    sol = subprocess.run([CADICAL, '-q', '--lrat=true', '--binary=true', path, fifo],
                         capture_output=True, text=True)
    out = chk.communicate()[0].strip()
    shutil.rmtree(d, ignore_errors=True)
    return sol.returncode, chk.returncode, out, time.time() - t0


DIGEST = re.compile(r'[0-9a-f]{16}|[0-9a-f]{64}')


def previous(path):
    """(name, r) -> (digest, verdict, seconds, file that solved it) for every scan line of an earlier
    output that was solved there, or reused there from a file that solved it. `digest` is what the
    solving run recorded (16 or 64 hex digits), so a reuse never strengthens the link."""
    out = {}
    for line in open(path):
        line = line.strip()
        m = re.match(r'(\S+) r=(\d+): sha256 ([0-9a-f]+) (.*)$', line)
        if not m or 's VERIFIED UNSAT' not in line or '--dump-cnf identical' not in line:
            continue
        name, r, digest, rest = m.group(1), int(m.group(2)), m.group(3), m.group(4)
        reused = re.match(r'= the CNF (\S+) solved \(recorded sha256 ([0-9a-f]+)\): ', rest)
        if reused:
            where, digest = reused.group(1), reused.group(2)
        elif rest.startswith('cadical exit 20; lratcheck exit 0: ') or \
                (rest.startswith('cadical exit 20; s VERIFIED') and 'lratcheck exit' not in rest):
            where = os.path.basename(path)       # (the second form: parts 1-2, before the exit code was printed)
        else:
            continue
        if not DIGEST.fullmatch(digest):
            continue
        i = rest.index('s VERIFIED UNSAT')
        verdict = rest[i:rest.index(';', i)]
        secs = float(re.search(r'\[([0-9.]+)s[^\]]*\]$', line).group(1))
        out[name, r] = (digest, verdict, secs, where)
    return out


def positive_control(tmp):
    """Unconditional: Lean's r = 13 CNF for the cube that came back SAT is the ledger's DIMACS, and
    the ledger's model satisfies every clause of it (the theorem's `cnf13_sat` is conditional)."""
    f = os.path.join(tmp, 'sat13.cnf')
    subprocess.run([EXPORT, 'sat13', f], check=True)
    data = open(f, 'rb').read()
    h = hashlib.sha256(data).hexdigest()
    line = [l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, 'ledger_mod3_6_1_13_s2_elim2_sem12_x_S_E.txt'))
            if l.split('\t')[0] == '42' and l.split('\t')[2] == 'SAT'][0]
    model = {int(x) for x in line[5].split()[1:]}
    clauses = [[int(x) for x in c.split()[:-1]] for c in data.decode().splitlines()[1:]]
    sat = all(any(l in model for l in c) for c in clauses)
    os.remove(f)
    print(f'positive control: Lean r=13 CNF of cube 42, {len(clauses)} clauses, sha256 {h[:16]} '
          f'{"=" if h == line[6] else "!="} ledger; the ledger\'s model satisfies '
          f'{"every clause" if sat else "NOT every clause"}', flush=True)
    return h == line[6] and sat


def main():
    prev = {}
    for i, a in enumerate(sys.argv):
        if a == '--resume':
            prev.update(previous(sys.argv[i + 1]))
    tmp = tempfile.mkdtemp(dir=os.environ.get('TMPDIR', '/scratch'))
    print(f'# sources: git {os.environ.get("REV", "(set REV to the commit the executables were built from)")}', flush=True)
    t_all = time.time()
    allok, nleaves = True, 0
    scans, splits = hypotheses()
    assert len(scans) + len(splits) == 22 and set(n for n, _, _ in splits) == set(LEDGER), 'hypothesis list'
    for name, _, expect in splits:
        ok, k = split_run(name, expect, tmp)
        allok &= ok
        nleaves += k
    t_split = time.time() - t_all
    allok &= positive_control(tmp)
    nscan, nprev, t_solve = 0, 0, 0.0
    for name, lo, hi in scans:
        for r in range(lo, hi + 1):
            f = os.path.join(tmp, f'{name}_{r}.cnf')
            subprocess.run([EXPORT, 'scan', name, str(r), f], check=True)
            h = hashlib.sha256(open(f, 'rb').read()).hexdigest()
            rt = dump_roundtrip(f)
            nscan += 1
            if (name, r) in prev and h.startswith(prev[name, r][0]):
                os.remove(f)
                rec, verdict, dt, where = prev[name, r]
                t_solve += dt
                nprev += 1
                allok &= rt
                print(f'  {name} r={r}: sha256 {h} = the CNF {where} solved (recorded sha256 {rec}): '
                      f'{verdict}; --dump-cnf {"identical" if rt else "DIFFERS"} [{dt:.1f}s there]', flush=True)
                continue
            code, ccode, out, dt = solve(f, tmp)
            os.remove(f)
            t_solve += dt
            good = code == 20 and ccode == 0 and out.startswith('s VERIFIED UNSAT') and rt
            allok &= good
            print(f'  {name} r={r}: sha256 {h} cadical exit {code}; lratcheck exit {ccode}: {out}; '
                  f'--dump-cnf {"identical" if rt else "DIFFERS"} [{dt:.1f}s]', flush=True)
    shutil.rmtree(tmp, ignore_errors=True)
    print(f'{"ALL CERTIFIED" if allok else "NOT ALL CERTIFIED"}: {nleaves} leaves by sha256 '
          f'[{t_split:.0f}s]; {nscan} scan CNFs exported, {nscan - nprev} solved here and Lean-checked'
          f'{f", {nprev} matched to the earlier run that solved them" if nprev else ""} '
          f'[{t_solve:.0f}s solve+check]; '
          f'total {time.time() - t_all:.0f}s wall', flush=True)
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
