/-
# A 13-gate B2 circuit for MOD3^1_6, hence also one for MOD3^2_6

The upper-bound half of `size(MOD3^{1,2}_6) = 13` (`research/circuits/RESULT.md`), stated in
`CircuitDual`'s bare model. The circuit is the one `research/circuits/r13_decode.py` decodes
from the r = 13 SAT model (`r13_decode.out`), copied gate by gate: node `6 + j` is gate `j`,
and each table is written `f00 f01 f10 f11` with the first bit index the gate's first input.

Proved:
* `mod3_1_upper`: `Computes 1 c13` (all 64 inputs, by `decide`), and `c13` has 13 gates.
* `mod3_2_upper`: some 13-gate list computes `MOD3^2_6` (via `mod3_6_size_dual`).

Not proved: the lower bound (no 12-gate circuit). That is the SAT refutation in
`research/circuits/`, which rests on prose soundness arguments for its constraints.
Kulikov–Pechenev–Slezkin (MFCS 2022) already published a 13-gate upper bound; this file is a
machine check of ours, not news.
-/
import Garden.CircuitDual

namespace Mod3Upper
open CircuitDual

/-- The 2-input table with truth values `f00 f01 f10 f11`. -/
def tbl (f00 f01 f10 f11 : Bool) (u v : Bool) : Bool :=
  match u, v with
  | false, false => f00
  | false, true => f01
  | true, false => f10
  | true, true => f11

def g (a b : ℕ) (f00 f01 f10 f11 : Bool) : Gate := ⟨a, b, tbl f00 f01 f10 f11⟩

/-- `r13_decode.out`, node 6 to node 18; output node 18, not negated. -/
def c13 : List Gate :=
  [ g 0 1   false true  true  false,   -- node 6:  0110
    g 0 1   false false false true,    -- node 7:  0001
    g 2 3   false true  true  false,   -- node 8:  0110
    g 4 7   false false true  false,   -- node 9:  0010
    g 6 9   false true  true  false,   -- node 10: 0110
    g 5 10  false true  true  false,   -- node 11: 0110
    g 3 11  false true  true  false,   -- node 12: 0110
    g 4 7   false true  true  false,   -- node 13: 0110
    g 8 12  false true  true  true,    -- node 14: 0111
    g 11 13 false true  true  false,   -- node 15: 0110
    g 10 15 false true  true  true,    -- node 16: 0111
    g 8 16  false true  true  false,   -- node 17: 0110
    g 14 17 false false false true ]   -- node 18: 0001

theorem c13_length : c13.length = 13 := rfl

theorem mod3_1_upper : Computes 1 c13 :=
  ⟨by simp [c13], by decide⟩

theorem mod3_2_upper : ∃ gs : List Gate, gs.length = 13 ∧ Computes 2 gs :=
  (mod3_6_size_dual c13).1 mod3_1_upper

end Mod3Upper
