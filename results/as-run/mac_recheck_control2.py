"""mac_recheck_control2.py (2026-10-25): one more runtime control for mac_recheck.py, run on the Mac as
`python3 -B run/mac_recheck_control2.py` beside ~/work/run/mac_recheck.py (imported, not changed).

In mac_recheck_controls.out, lratdirect rejected leaf full6_12 6844's proof given as leaf 6845 at parse:
6845's CNF has one clause more, so the proof's first clause id is already wrong. Here the other leaf is
the nearest one with the same base (tag), the same DIMACS header (so the same number of variables and
clauses) and a different cube, so both checkers must get past the clause count and fail on the proof
itself. Leaf 6844's proof must first be accepted by both for its own leaf.

A rejection counts only if it is explicit: cake_lpr not killed by a signal, its stdout not the success
line, and its `Checking failed` message present; lratdirect exiting 1 with one `s NOT VERIFIED (` line.
A crash is not a rejection. The pins are checked first (the binaries must be the run's). Exit 0 only if
the control passed.

Revised after review: the first version (committed in e2740ae, same leaves, same verdicts) did not
check pins, counted any non-acceptance as a rejection, and exited 0 either way.
"""
import os, shutil, sys, tempfile

sys.path.insert(0, os.path.expanduser('~/work/run'))
import mac_recheck as m


def cake_rejects(k):
    code, out, tail = k[0], k[1], k[2]
    return code >= 0 and out != b's VERIFIED UNSAT\n' and (b'Checking failed' in out or 'Checking failed' in tail)


def direct_rejects(x):
    code, out = x[0], x[1].decode(errors='replace').strip()
    return code == 1 and out.startswith('s NOT VERIFIED (') and '\n' not in out


pins = m.check_pins()
print('pins %s (the run\'s session header names the same)' % pins)
by = {(j['kind'], j['run'], j['i']): j for j in m.jobs()}
a = by['leaf', 'full6_12', 6844]
same = [j for j in by.values() if j['kind'] == 'leaf' and j['run'] == 'full6_12' and j['i'] != a['i']
        and j['tag'] == a['tag'] and j['hdr'] == a['hdr'] and j['cube'] != a['cube']]
b = min(same, key=lambda j: abs(j['i'] - a['i']))
d = tempfile.mkdtemp(dir=m.TMP, prefix='ctl2-')
ok = False
try:
    fa, fb, proof = (os.path.join(d, x) for x in ('a.cnf', 'b.cnf', 'proof.lrat'))
    m.write_cnf(a, fa)
    m.write_cnf(b, fb)
    print('%s: header %s, cube %s; %s: header %s, cube %s' % (a['label'], a['hdr'], a['cube'], b['label'],
                                                              b['hdr'], b['cube']), flush=True)
    c = m.proc([m.CADICAL, '-q', '--lrat=true', '--binary=true', fa, proof], d)
    k0 = m.proc([m.CAKE, fa, proof], d, m.CAKE_ENV)
    x0 = m.proc([m.DIRECT] + m.direct_args(a) + [proof], d)
    base = (c[0] == 20 and m.cake_verdict(*k0[:3])[0] and m.direct_verdict(*x0[:3], a['label'])[0]
            and m.sha256(fa) in a['want'] and m.sha256(fb) in b['want'])
    print('base: %s: cadical exit %d; cake_lpr %s; lratdirect %s -> %s'
          % (a['label'], c[0], m.cake_verdict(*k0[:3])[1], m.direct_verdict(*x0[:3], a['label'])[1],
             'accepted by both' if base else 'NOT ACCEPTED'))
    k = m.proc([m.CAKE, fb, proof], d, m.CAKE_ENV)
    x = m.proc([m.DIRECT] + m.direct_args(b) + [proof], d)
    good = cake_rejects(k) and direct_rejects(x)
    print('  proof of %s given as %s: cake_lpr exit %d: %s; lratdirect exit %d: %s -> %s'
          % (a['label'], b['label'], k[0], (k[1].decode(errors='replace').strip() or k[2])[:200], x[0],
             x[1].decode(errors='replace').strip()[:300], 'both rejected explicitly' if good else 'NOT BOTH REJECTED'))
    ok = base and good
    print('CONTROL %s' % ('PASSED' if ok else 'FAILED'))
finally:
    shutil.rmtree(d, ignore_errors=True)
sys.exit(0 if ok else 1)
