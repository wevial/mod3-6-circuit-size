/-
# The `w2_5^1` runs' `semrows` bounds, proved from `GateElim.sem_bound`

`size(w2_5^1) ≥ 10` (the bound `semeq` uses at n = 6) was certified at r = 8, 9 by
`w2cubes.py` with `semrows = sem_general(|S| = 1, 2) + sem_pairs`. Each row set `T` there gets
the clause `redundancy(T, r − size(h))`, `h` what `w2_5^1` becomes on `T`, its size computed by
`_restricted_size`. This file proves every one of those 70 inequalities for **every** circuit
computing `w2_5^1`, with the sizes of the `h` as hypotheses (`Mod3Tower` discharges them):

* `sem_general`, |S| = 1, rows `x_v = c` (`semGen`, `sW1`): `h` is `MOD3_4^{1,2}` (`v = 0`) or
  `w2_4^{1,0}` (`v ≥ 1`), sizes 7, 6 / 6, 7;
* `sem_general`, |S| = 2, rows `x_u = a, x_v = b` (`sW2`): `MOD3_3^q` (`u = 0`) or `w2_3^q`;
* `sem_pairs`, rows `x_v = c ⊕ x_u`, `u < v` (`semPairs`, `sWP`): `MOD3_3^1` with a dummy input
  (`u = 0`, `c = 0`, size 4), `MOD3_4^0` (`u = 0`, `c = 1`, 7), `pq` up to a permutation of its
  inputs (`u ≥ 1`, `c = 0`, 7), `w2_3^0` with a dummy input (`u ≥ 1`, `c = 1`, 4).

`sW1`, `sW2`, `sWP` are the numbers `sem_general`/`sem_pairs` produce: on 2026-10-24 a script
compared `r − sW…` with their output at r = 8 and 9, row set by row set, and found them equal (and
the r = 8, 9 ledgers' DIMACS sha256 values, which contain these bounds, regenerate exactly; see
`research/log/`).

Finite facts by `decide +kernel`. Axioms: the standard three.
-/
import Garden.Tower

namespace W2SemBounds
open CircuitDual GateElim Mod3SemBounds Tower

/-- `w2_m^q = [2 y0 + y1 + … ≡ q mod 3]`, `FUNCS['w2_m_q']`. -/
def wq (q : ℕ) (y : List Bool) : Bool :=
  decide ((2 * (y.getD 0 false).toNat + ((y.drop 1).map Bool.toNat).sum) % 3 = q)

theorem w2_eq : w2 = wq 1 := rfl

/-- `[2 y0 + 2 y1 + y2 + y3 ≡ 1 mod 3]`: `w2_5^1` under `x_v := x_u`, `1 ≤ u < v`, up to order. -/
def pq (y : List Bool) : Bool :=
  decide ((2 * (y.getD 0 false).toNat + 2 * (y.getD 1 false).toNat +
    ((y.drop 2).map Bool.toNat).sum) % 3 = 1)

/-- Certified sizes of `MOD3_3^q` (`CERTIFIED`) and `w2_3^q` (`_restricted_size`). -/
def c3 (q : ℕ) : ℕ := [3, 4, 4].getD q 0
def cw3 (q : ℕ) : ℕ := [4, 4, 3].getD q 0

/-- `sem_general`'s size for rows `x_v = c`. -/
def sW1 (v : ℕ) (c : Bool) : ℕ := if v = 0 then (if c then 6 else 7) else (if c then 7 else 6)

/-- `sem_general`'s size for rows `x_u = a, x_v = b`, `u < v`. -/
def sW2 (u : ℕ) (a b : Bool) : ℕ :=
  if u = 0 then c3 ((7 - 2 * a.toNat - b.toNat) % 3) else cw3 ((7 - a.toNat - b.toNat) % 3)

/-- `sem_pairs`' size for rows `x_v = c ⊕ x_u`, `u < v`. -/
def sWP (u : ℕ) (c : Bool) : ℕ := if u = 0 then (if c then 7 else 4) else (if c then 4 else 7)

/-- The rows `x_v = c ⊕ x_u` (`sem_pairs`: `x_u ⊕ x_v = c`). -/
def rowsP (n u v : ℕ) (c : Bool) : Set (List Bool) :=
  {x | x.length = n ∧ x.getD v false = (c ^^ x.getD u false)}

/-- The `semrows` of `sem_general(w2_5_1, r, (1, 2))`, as `(T, size)`. -/
def semGen (T : Set (List Bool)) (s : ℕ) : Prop :=
  (∃ v < 5, ∃ c : Bool, T = rows1 5 v c ∧ s = sW1 v c) ∨
  (∃ u < 5, ∃ v < 5, u < v ∧ ∃ a b : Bool, T = rows2 5 u v a b ∧ s = sW2 u a b)

/-- The `semrows` of `sem_pairs(w2_5_1, r)`, as `(T, size)`. -/
def semPairs (T : Set (List Bool)) (s : ℕ) : Prop :=
  ∃ u < 5, ∃ v < 5, u < v ∧ ∃ c : Bool, T = rowsP 5 u v c ∧ s = sWP u c

/-! ### Substitutions and the functions they leave -/

/-- `x_v := c ⊕ x_u`; the other inputs keep their order (`sem_pairs`' `rest`). -/
def pairV (n u v : ℕ) (c : Bool) : List Rep :=
  (List.range n).map fun i => if i = v then .lit u c else .lit (if i < v then i else i - 1) false

/-- What `w2_5^1` becomes on `x_v = c`, up to nothing: the representative itself. -/
def rep1 (v : ℕ) (c : Bool) : List Bool → Bool :=
  if v = 0 then (if c then mod3 2 else mod3 1) else (if c then wq 0 else wq 1)

def rep2 (u : ℕ) (a b : Bool) : List Bool → Bool :=
  if u = 0 then mod3 ((7 - 2 * a.toNat - b.toNat) % 3) else wq ((7 - a.toNat - b.toNat) % 3)

/-- Drop input 0 (a dummy): 4 inputs from 3. -/
def drop0 : List Rep := [.const false, .lit 0 false, .lit 1 false, .lit 2 false]

/-- Move input `u` to position 1. -/
def front (u : ℕ) : List Rep :=
  (List.range 4).map fun i => if i = 0 then .lit 0 false else if i = u then .lit 1 false
    else if i < u then .lit (i + 1) false else .lit i false

/-- Drop input `u` (a dummy). -/
def dropAt (u : ℕ) : List Rep :=
  (List.range 4).map fun i => if i = 0 then .lit 0 false else if i = u then .const false
    else if i < u then .lit i false else .lit (i - 1) false

def id4 : List Rep := subPat 4 fun _ => none
def id3 : List Rep := subPat 3 fun _ => none

set_option synthInstance.maxSize 1024

theorem chk_ids : (∀ i < 4, (sig id4 i).Lt 4) ∧ (∀ i < 3, (sig id3 i).Lt 3) ∧
    (∀ i < 4, (sig drop0 i).Lt 3) ∧ (∀ u < 4, (∀ i < 4, (sig (front u) i).Lt 4)) ∧
    (∀ u < 4, 0 < u → ∀ i < 4, (sig (dropAt u) i).Lt 3) := by
  decide +kernel

/-! ### `sem_general`, |S| = 1 -/

theorem chk_w1 : ∀ v < 5, ∀ c : Bool,
    (∀ y ∈ allRows 4, (inRow 5 (sig (subPat 5 (fix1 v c))) y).getD v false = c) ∧
    (∀ x ∈ allRows 5, x.getD v false = c →
      (x.eraseIdx v).length = 4 ∧ x = inRow 5 (sig (subPat 5 (fix1 v c))) (x.eraseIdx v)) ∧
    (∀ i < 5, (sig (subPat 5 (fix1 v c)) i).Lt 4) ∧
    (∀ z ∈ allRows 4, w2 (inRow 5 (sig (subPat 5 (fix1 v c))) (inRow 4 (sig id4) z)) = rep1 v c z) ∧
    (∀ b : Bool, ∃ y ∈ allRows 4, w2 (inRow 5 (sig (subPat 5 (fix1 v c))) y) ≠ b) ∧
    (∀ k < 4, ∀ b : Bool, ∃ y ∈ allRows 4,
      w2 (inRow 5 (sig (subPat 5 (fix1 v c))) y) ≠ (b ^^ y.getD k false)) := by
  decide +kernel

/-! ### `sem_general`, |S| = 2 -/

theorem chk_w2 : ∀ u < 5, ∀ v < 5, u < v → ∀ a b : Bool,
    (∀ y ∈ allRows 3, (inRow 5 (sig (subPat 5 (fix2 u v a b))) y).getD u false = a ∧
      (inRow 5 (sig (subPat 5 (fix2 u v a b))) y).getD v false = b) ∧
    (∀ x ∈ allRows 5, (x.getD u false = a ∧ x.getD v false = b) →
      ((x.eraseIdx v).eraseIdx u).length = 3 ∧
      x = inRow 5 (sig (subPat 5 (fix2 u v a b))) ((x.eraseIdx v).eraseIdx u)) ∧
    (∀ i < 5, (sig (subPat 5 (fix2 u v a b)) i).Lt 3) ∧
    (∀ z ∈ allRows 3, w2 (inRow 5 (sig (subPat 5 (fix2 u v a b))) (inRow 3 (sig id3) z)) =
      rep2 u a b z) ∧
    (∀ c : Bool, ∃ y ∈ allRows 3, w2 (inRow 5 (sig (subPat 5 (fix2 u v a b))) y) ≠ c) ∧
    (∀ k < 3, ∀ c : Bool, ∃ y ∈ allRows 3,
      w2 (inRow 5 (sig (subPat 5 (fix2 u v a b))) y) ≠ (c ^^ y.getD k false)) := by
  decide +kernel

/-! ### `sem_pairs` -/

/-- The row set, the substitution's range, and that `w2 ∘ pairV` is not constant or a literal. -/
theorem chk_pset : ∀ u < 5, ∀ v < 5, u < v → ∀ c : Bool,
    (∀ y ∈ allRows 4, (inRow 5 (sig (pairV 5 u v c)) y).getD v false =
      (c ^^ (inRow 5 (sig (pairV 5 u v c)) y).getD u false)) ∧
    (∀ x ∈ allRows 5, x.getD v false = (c ^^ x.getD u false) →
      (x.eraseIdx v).length = 4 ∧ x = inRow 5 (sig (pairV 5 u v c)) (x.eraseIdx v)) ∧
    (∀ i < 5, (sig (pairV 5 u v c) i).Lt 4) ∧
    (∀ b : Bool, ∃ y ∈ allRows 4, w2 (inRow 5 (sig (pairV 5 u v c)) y) ≠ b) ∧
    (∀ k < 4, ∀ b : Bool, ∃ y ∈ allRows 4,
      w2 (inRow 5 (sig (pairV 5 u v c)) y) ≠ (b ^^ y.getD k false)) := by
  decide +kernel

/-- What `w2 ∘ pairV` is, in each of the four cases. -/
theorem chk_pfun :
    (∀ v < 5, 0 < v → ∀ z ∈ allRows 3,
      w2 (inRow 5 (sig (pairV 5 0 v false)) (inRow 4 (sig drop0) z)) = mod3 1 z) ∧
    (∀ v < 5, 0 < v → ∀ z ∈ allRows 4,
      w2 (inRow 5 (sig (pairV 5 0 v true)) (inRow 4 (sig id4) z)) = mod3 0 z) ∧
    (∀ u < 5, ∀ v < 5, 0 < u → u < v → ∀ z ∈ allRows 4,
      w2 (inRow 5 (sig (pairV 5 u v false)) (inRow 4 (sig (front u)) z)) = pq z) ∧
    (∀ u < 5, ∀ v < 5, 0 < u → u < v → ∀ z ∈ allRows 3,
      w2 (inRow 5 (sig (pairV 5 u v true)) (inRow 4 (sig (dropAt u)) z)) = wq 0 z) := by
  decide +kernel

/-! ### The bounds -/

/-- **Every `semrows` inequality of the `w2_5^1` runs holds in every circuit for `w2_5^1`**,
given the sizes of the restricted functions. -/
theorem w2_sem_bounds
    (h3 : ∀ q < 3, LB 3 (mod3 q) (c3 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw3 : ∀ q < 3, LB 3 (wq q) (cw3 q)) (hw40 : LB 4 (wq 0) 7) (hw41 : LB 4 (wq 1) 6)
    (hpq : LB 4 pq 7) :
    ∀ T s, (semGen T s ∨ semPairs T s) → SemOK 5 w2 T s := by
  obtain ⟨hid4, hid3, hd0, hfr, hdr⟩ := chk_ids
  rintro T s ((⟨v, hv, c, rfl, rfl⟩ | ⟨u, hu, v, hv, huv, a, b, rfl, rfl⟩) |
    ⟨u, hu, v, hv, huv, c, rfl, rfl⟩)
  · obtain ⟨hA, hB, hσ, hfg, hc, hl⟩ := chk_w1 v hv c
    have hlb : LB 4 (rep1 v c) (sW1 v c) := by
      unfold rep1 sW1
      split_ifs
      exacts [h4 2 (by omega), h4 1 (by omega), hw40, hw41]
    exact semOK_of 5 4 _ w2 (fun x => x.getD v false = c) (fun x => x.eraseIdx v) _ hA hB hσ hc hl
      (lb_transfer 4 4 _ hid4 _ _ _ hfg hlb)
  · obtain ⟨hA, hB, hσ, hfg, hc, hl⟩ := chk_w2 u hu v hv huv a b
    have hlb : LB 3 (rep2 u a b) (sW2 u a b) := by
      unfold rep2 sW2
      split_ifs
      exacts [h3 _ (Nat.mod_lt _ (by omega)), hw3 _ (Nat.mod_lt _ (by omega))]
    exact semOK_of 5 3 _ w2 (fun x => x.getD u false = a ∧ x.getD v false = b)
      (fun x => (x.eraseIdx v).eraseIdx u) _ hA hB hσ hc hl
      (lb_transfer 3 3 _ hid3 _ _ _ hfg hlb)
  · obtain ⟨hA, hB, hσ, hc, hl⟩ := chk_pset u hu v hv huv c
    obtain ⟨p1, p2, p3, p4⟩ := chk_pfun
    have hlb : LB 4 (fun y => w2 (inRow 5 (sig (pairV 5 u v c)) y)) (sWP u c) := by
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · cases c
        · exact lb_transfer 4 3 _ hd0 _ _ _ (p1 v hv huv) (h3 1 (by omega))
        · exact lb_transfer 4 4 _ hid4 _ _ _ (p2 v hv huv) (h4 0 (by omega))
      · have hne : u ≠ 0 := by omega
        cases c
        · simp only [sWP, if_neg hne]
          exact lb_transfer 4 4 _ (hfr u (by omega)) _ _ _ (p3 u hu v hv hu0 huv) hpq
        · simp only [sWP, if_neg hne]
          exact lb_transfer 4 3 _ (hdr u (by omega) hu0) _ _ _ (p4 u hu v hv hu0 huv) (hw3 0 (by omega))
    exact semOK_of 5 4 _ w2 (fun x => x.getD v false = (c ^^ x.getD u false)) (fun x => x.eraseIdx v)
      _ hA hB hσ hc hl hlb

end W2SemBounds
