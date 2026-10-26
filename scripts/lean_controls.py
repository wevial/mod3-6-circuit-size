"""lean_controls.py: run the Lean controls in lean/controls/ and check each one fails as it should.

    python3 scripts/lean_controls.py        (from the repository root, after the Lean build)

* The two `*-must-fail.lean` files hold 35 controls, `K1`–`K15` and `D1`–`D20`. Each is a theorem
  whose statement has been mutated, keeping the original proof (verbatim, or adapted only to the
  mutated shape); each comment says what changed. Every control must FAIL, and the error that Lean
  reports inside its declaration must be the one its mutation causes: `EXPECTED` below gives, for each
  control, a pattern for that diagnostic. Further errors inside a control are reported but allowed.
  An error outside every control (an import, a helper `def`) fails the check, since a broken file
  would make every control fail for the wrong reason.
* The two `*-witness.lean` files must build with no error. They show that several mutated claims
  are false, not merely unprovable by the reused proof.
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean')
MUST_FAIL = ['controls/2026-10-24-cnf-must-fail.lean', 'controls/2026-10-25-direct-must-fail.lean']
WITNESS = ['controls/2026-10-24-cnf-witness.lean', 'controls/2026-10-25-direct-witness.lean']

# The diagnostic each mutation causes (the "fails at" column of the controls' tables in the
# research logs of 2026-10-24 23:01 and 2026-10-25 04:30), as a regex over the full error message.
EXPECTED = {
    'K1': r'unsolved goals',                                      # flipped literal: membership goal left
    'K2': r'`assumption` failed[\s\S]*⊢ Good ev e',               # numbering lemma without `Good`
    'K3': r'expected to have type\s+\(Mod3Tower\.best 6\)\.elim = some',
    'K4': r'Type mismatch[\s\S]*Mod3Tower\.elim6\.',
    'K5': r'unsolved goals[\s\S]*cubeCnf',
    'K6': r'unsolved goals[\s\S]*\(A\.length \+ B\.length\) \+\+ body A \+\+ body B =[\s\S]*\) A\.length \+\+ body A',
    'K7': r'`decide` proved that the proposition[\s\S]*mod3 2[\s\S]*is false',
    'K8': r'unsolved goals[\s\S]*⊢ ∃ ch ∈ lv',
    'K9': r'unsolved goals\s+case true\.true\.true[\s\S]*⊢ False',  # the table cube (1,1,1) left out
    'K10': r'argument\s+h12\s+has type',
    'K11': r'ScanUnsat \(CnfSpecs\.best 5 0\) 1 7\s+but is expected to have type[\s\S]* 1 8',
    'K12': r'LB 6 \(mod3 1\) 13\s+but is expected to have type\s+LB 6 \(mod3 1\) 14',
    'K13': r'omega could not prove the goal',
    'K14': r'scanList\.tail, ScanUnsat[\s\S]*expected to have type\s+∀ x ∈ CnfSpecs\.scanList, ',
    'K15': r'`decide` proved that the proposition\s+\("best4_0" ::[\s\S]*is false',
    'D1': r'unsolved goals[\s\S]*⊢ r ≤ x\.hi',
    'D2': r'unsolved goals[\s\S]*match x\.leaves\[i\]\? with',
    'D3': r'List\.find\? \S+ scanList\.tail = some x',
    'D4': r'List\.find\? \S+ splitList\.tail = some x',
    'D5': r'List\.foldl advance \(stepChunk f c 0\) cs = Sum\.inr f',
    'D6': r'⊢ runChunks f \[\] = Result\.success',
    'D7': r'\[\(st\.ps\.parse b\)\.2\]\.length = 0',
    'D8': r'\[st\.ps\.close\.2\]\.length = 0',
    'D9': r'⊢ List\.foldl advance st\.fs cs₁ = st\.fs',
    'D10': r'`rfl` failed[\s\S]*Sum\.inl Result\.rupFailure',
    'D11': r'= Result\.success ∨ \S+ = Result\.outOfProof → \S+ = Result\.success',
    'D12': r'match j\.cnf\? with[\s\S]*expected to have type\s+\(check \(toCNF F\) bs\)\.verified = true',
    'D13': r'x\.lo ≤ r\s+but is expected to have type\s+x\.lo ≤ r \+ 1',
    'D14': r'expected to have type\s+\(checkJob \(Job\.leaf name \(i \+ 1\)\) bs\)\.verified',
    'D15': r'unsolved goals[\s\S]*⊢ y = x',
    'D16': r'scanList \+\+ \[\{ name := "best3_0"',
    'D17': r'splitList \+\+ \[\{ name := "cube5_0"',
    'D18': r'r ≤ x\.hi\s+but is expected to have type\s+r < x\.hi',
    'D19': r'i < x\.leaves\.length\s+but is expected to have type\s+i \+ 1 < x\.leaves\.length',
    'D20': r'LB 6 \(mod3 1\) 13\s+but is expected to have type\s+LB 6 \(mod3 1\) 14',
}
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure|inductive|section|end|namespace)\b\s*(\S*)')
CONTROL = re.compile(r'^([KD]\d+)_\w*$')
MSG = re.compile(r'^\S+\.lean:(\d+):(\d+): (error|warning|info): ', re.M)


def run(path):
    """Exit code and the (line, full message) of every error Lean reports for one file."""
    p = subprocess.run(['lake', 'env', 'lean', path], cwd=LEAN, capture_output=True, text=True)
    out = p.stdout + p.stderr
    starts = list(MSG.finditer(out))
    errors = []
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(out)
        if m.group(3) == 'error':
            errors.append((int(m.group(1)), out[m.end():end].strip()))
    return p.returncode, errors, out


def main():
    ok = True
    present = sorted('controls/' + f for f in os.listdir(os.path.join(LEAN, 'controls')))
    if present != sorted(MUST_FAIL + WITNESS):
        print('lean/controls/ holds %s, expected %s' % (present, sorted(MUST_FAIL + WITNESS)))
        ok = False
    for rel in WITNESS:
        code, errors, out = run(rel)
        good = code == 0 and not errors
        print('%s: %s (exit %d, %d errors)' % (rel, 'builds, as required' if good else 'DOES NOT BUILD', code,
                                               len(errors)))
        if not good:
            print(out[-3000:])
        ok &= good
    seen = set()
    for rel in MUST_FAIL:
        lines = open(os.path.join(LEAN, rel)).read().splitlines()
        code, errors, out = run(rel)
        decls = [(n, m.group(1), m.group(2)) for n, line in enumerate(lines, 1) for m in [DECL.match(line)] if m]
        controls = [(n, CONTROL.match(name).group(1), name) for n, kind, name in decls
                    if kind == 'theorem' and CONTROL.match(name)]
        by_control, stray = {}, []
        for n, msg in errors:
            owner = max((d for d in decls if d[0] <= n), default=None)
            c = CONTROL.match(owner[2]) if owner and owner[1] == 'theorem' else None
            if c:
                by_control.setdefault(c.group(1), []).append((n, msg))
            else:
                stray.append((n, msg.splitlines()[0]))
        print('%s: exit %d, %d controls' % (rel, code, len(controls)))
        if code == 0:
            ok = False
        for _, tag, name in controls:
            seen.add(tag)
            errs = by_control.get(tag, [])
            pat = EXPECTED.get(tag)
            hit = [n for n, msg in errs if pat and re.search(pat, msg)]
            other = [(n, msg.splitlines()[0]) for n, msg in errs if n not in hit]
            if hit:
                status = 'fails as intended (line %d)' % hit[0]
                if other:
                    status += '; also: ' + '; '.join('line %d: %s' % e for e in other)
            else:
                status = 'DOES NOT FAIL AS INTENDED: ' + ('; '.join('line %d: %s' % e for e in other)
                                                          or 'no error')
                ok = False
            print('  %-34s %s' % (name, status[:200]))
        for n, first in stray:
            print('  ERROR OUTSIDE ANY CONTROL, line %d: %s' % (n, first))
            ok = False
    missing = sorted(set(EXPECTED) - seen)
    if missing:
        print('controls not found: %s' % ', '.join(missing))
        ok = False
    print('LEAN CONTROLS %s' % ('PASSED: all %d must-fail controls fail with their intended error, both '
                                'witness files build' % len(EXPECTED) if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
