/-
# The r = 12 run's `sem`/`semxor`/`semeq` bounds for MOD3^1_6, proved from `GateElim.sem_bound`

`GateElim.sem_bound` is the general inequality. This file instantiates it at exactly the row sets
and numbers `optimal_circuit.encode` received in the r = 12 run (`SEM=1,2 SEMXOR=1 SEMEQ=1`):

* `sem`, |S| = 1: rows `x_v = c`, bound `r − size(MOD3_5^{(1−c) mod 3})` (10, 9, 10);
* `sem`, |S| = 2: rows `x_u = a, x_v = b`, bound `r − size(MOD3_4^{(1−a−b) mod 3})` (7, 7, 6);
* `semxor`: rows `x_u ≠ x_v`, bound `r − size(MOD3_4^0)` (7);
* `semeq`: rows `x_u = x_v`, bound `r − 10`, from `size(w2_5^1) ≥ 10`.

`mod3_6_1_sem_bounds` proves all four families for **every** nonempty circuit computing `MOD3^1_6`,
with `r = gs.length`. The finite facts (each row set is the image of a substitution, each
substituted function is the claimed smaller one up to renaming, none is constant or a literal) are
checked by `decide +kernel` over all `u < v < 6` and all constants.

Hypotheses, not proved here: the lower bounds `LB 5 (mod3 q) (c5 q)`, `LB 4 (mod3 q) (c4 q)`,
`LB 5 w2 10`, the SAT-certified sizes (`CERTIFIED`, `W2_LOWER`), stated in this file's circuit
model. Since 2026-10-24 they are proved from their own runs' SAT sides in `Mod3Tower.lean` (`lb5`,
`lb4`, `lbw2`), and the move between this model and the CNF's is proved there too
(`Reduction.minimal_canonical_on`, `Tower.lower`); it was by eye before.

Also by eye: the CNF's `redundancy` clauses encode `GateElim.Redundant` with the bound `B`.
`elim`/`elim2` count only gates that are redundant under the same restriction, by `encode`'s
docstring, so their bounds are these bounds for |S| = 1, 2.

Controls (each must fail, and does): `(5 − c) mod 3` in place of `(4 − c) mod 3` in `chk_sub1`; `w2`
with residue 2; the `semeq` conjunct with 11 in place of 10.
-/
import Garden.GateElim

namespace Mod3SemBounds
open CircuitDual GateElim

/-- Every circuit computing `g` on `m`-bit rows has at least `s` gates. -/
def LB (m : ℕ) (g : List Bool → Bool) (s : ℕ) : Prop :=
  ∀ gs : List Gate, gs ≠ [] → (∀ y : List Bool, y.length = m → out y gs = g y) → s ≤ gs.length

def allRows : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allRows m).flatMap fun l => [false :: l, true :: l]

lemma mem_allRows : ∀ (y : List Bool) (m : ℕ), y.length = m → y ∈ allRows m := by
  intro y
  induction y with
  | nil => intro m h; subst h; simp [allRows]
  | cons b y ih =>
    intro m h; subst h
    simp only [allRows, List.length_cons, List.mem_flatMap]
    exact ⟨y, ih _ rfl, by cases b <;> simp⟩

lemma length_of_mem_allRows : ∀ (m : ℕ) (y : List Bool), y ∈ allRows m → y.length = m := by
  intro m
  induction m with
  | zero => intro y hy; simpa [allRows] using hy
  | succ m ih =>
    intro y hy
    simp only [allRows, List.mem_flatMap] at hy
    obtain ⟨l, hl', hy⟩ := hy
    have := ih l hl'; simp at hy; rcases hy with rfl | rfl <;> simp [this]

instance (m : ℕ) : DecidablePred (Rep.Lt m) := fun r => by
  cases r <;> simp only [Rep.Lt] <;> infer_instance

/-- The substitution given by a list: old input `i` becomes `p[i]`. -/
def sig (p : List Rep) (i : ℕ) : Rep := p.getD i (.const false)

lemma inRow_length (n : ℕ) (σ : ℕ → Rep) (y : List Bool) : (inRow n σ y).length = n := by
  simp [inRow]

/-- Lower bounds transfer along a substitution `τ` from `m'` to `m` inputs. -/
lemma lb_transfer (m m' : ℕ) (τ : ℕ → Rep) (hτ : ∀ i < m, (τ i).Lt m') (g h : List Bool → Bool)
    (s : ℕ) (hgh : ∀ z ∈ allRows m', g (inRow m τ z) = h z) (hlb : LB m' h s) : LB m g s := by
  intro gs hne hgs
  have := hlb (gs.map (substGate m m' τ)) (by simpa using hne) (fun z hz => by
    rw [subst_out m m' τ hτ gs hne z hz, hgs _ (inRow_length _ _ _), hgh z (mem_allRows z m' hz)])
  simpa using this

/-- `sem_bound` with every side condition a finite check. -/
lemma bound_of_pattern (n m : ℕ) (p : List Rep) (f : List Bool → Bool) (s : ℕ)
    (hσ : ∀ i < n, (sig p i).Lt m)
    (hc : ∀ c : Bool, ∃ y ∈ allRows m, f (inRow n (sig p) y) ≠ c)
    (hl : ∀ k < m, ∀ b : Bool, ∃ y ∈ allRows m, f (inRow n (sig p) y) ≠ (b ^^ y.getD k false))
    (hlb : LB m (fun y => f (inRow n (sig p) y)) s)
    (gs : List Gate) (hne : gs ≠ []) (hgs : ∀ x : List Bool, x.length = n → out x gs = f x) :
    redCount n gs {x | ∃ y : List Bool, y.length = m ∧ x = inRow n (sig p) y} + s ≤ gs.length := by
  apply sem_bound n m (sig p) hσ f gs hne hgs s
  · rintro ⟨c, h⟩
    obtain ⟨y, hy, hne'⟩ := hc c
    exact hne' (h y (length_of_mem_allRows m y hy))
  · rintro ⟨k, hk, b, h⟩
    obtain ⟨y, hy, hne'⟩ := hl k hk b
    exact hne' (h y (length_of_mem_allRows m y hy))
  · exact hlb

/-! ### The patterns `optimal_circuit.encode` uses at n = 6 -/

/-- Fix the inputs where `fix i = some c`, rename the free ones `0, 1, …` in order. -/
def subPat (n : ℕ) (fix : ℕ → Option Bool) : List Rep :=
  (List.range n).map fun i => match fix i with
    | some c => .const c
    | none => .lit ((List.range i).countP fun j => (fix j).isNone) false

def fix1 (v : ℕ) (c : Bool) (i : ℕ) : Option Bool := if i = v then some c else none
def fix2 (u v : ℕ) (a b : Bool) (i : ℕ) : Option Bool :=
  if i = u then some a else if i = v then some b else none

/-- `x_u := (neg ⊕ x_v)`, `u < v`; the other inputs keep their order. -/
def pairPat (n u v : ℕ) (neg : Bool) : List Rep :=
  (List.range n).map fun i => if i = u then .lit (v - 1) neg else .lit (if i < u then i else i - 1) false

/-- `w2_5^1 = [2 y0 + y1 + … + y4 ≡ 1 mod 3]`, the function `semeq` leaves (`W2_LOWER`). -/
def w2 (y : List Bool) : Bool := decide ((2 * (y.getD 0 false).toNat +
  ((y.drop 1).map Bool.toNat).sum) % 3 = 1)

/-- semeq's renaming: the merged input `v − 1` goes to `w2`'s weight-2 slot. -/
def eqPerm (v : ℕ) : List Rep :=
  (List.range 5).map fun j => .lit (if j = v - 1 then 0 else if j < v - 1 then j + 1 else j) false

/-- Certified sizes used as hypotheses (`CERTIFIED` in `optimal_circuit.py`). -/
def c5 (q : ℕ) : ℕ := [10, 9, 10].getD q 0
def c4 (q : ℕ) : ℕ := [7, 7, 6].getD q 0

def f1 : List Bool → Bool := mod3 1

/-! Finite checks, by `decide` (kernel). -/

set_option synthInstance.maxSize 1024

theorem chk_sub1 : ∀ v < 6, ∀ c : Bool,
    (∀ i < 6, (sig (subPat 6 (fix1 v c)) i).Lt 5) ∧
    (∀ z ∈ allRows 5, f1 (inRow 6 (sig (subPat 6 (fix1 v c))) (inRow 5 (sig (subPat 5 fun _ => none)) z))
        = mod3 ((4 - c.toNat) % 3) z) ∧
    (∀ b : Bool, ∃ y ∈ allRows 5, f1 (inRow 6 (sig (subPat 6 (fix1 v c))) y) ≠ b) ∧
    (∀ k < 5, ∀ b : Bool, ∃ y ∈ allRows 5,
      f1 (inRow 6 (sig (subPat 6 (fix1 v c))) y) ≠ (b ^^ y.getD k false)) := by
  decide +kernel


theorem chk_sub2 : ∀ u < 6, ∀ v < 6, u < v → ∀ a b : Bool,
    (∀ i < 6, (sig (subPat 6 (fix2 u v a b)) i).Lt 4) ∧
    (∀ z ∈ allRows 4, f1 (inRow 6 (sig (subPat 6 (fix2 u v a b))) (inRow 4 (sig (subPat 4 fun _ => none)) z))
        = mod3 ((7 - a.toNat - b.toNat) % 3) z) ∧
    (∀ c : Bool, ∃ y ∈ allRows 4, f1 (inRow 6 (sig (subPat 6 (fix2 u v a b))) y) ≠ c) ∧
    (∀ k < 4, ∀ c : Bool, ∃ y ∈ allRows 4,
      f1 (inRow 6 (sig (subPat 6 (fix2 u v a b))) y) ≠ (c ^^ y.getD k false)) := by
  decide +kernel


theorem chk_xor : ∀ u < 6, ∀ v < 6, u < v →
    (∀ i < 6, (sig (pairPat 6 u v true) i).Lt 5) ∧
    (∀ i < 5, (sig (subPat 5 (fix1 (v - 1) false)) i).Lt 4) ∧
    (∀ z ∈ allRows 4, f1 (inRow 6 (sig (pairPat 6 u v true)) (inRow 5 (sig (subPat 5 (fix1 (v - 1) false))) z))
        = mod3 0 z) ∧
    (∀ c : Bool, ∃ y ∈ allRows 5, f1 (inRow 6 (sig (pairPat 6 u v true)) y) ≠ c) ∧
    (∀ k < 5, ∀ c : Bool, ∃ y ∈ allRows 5,
      f1 (inRow 6 (sig (pairPat 6 u v true)) y) ≠ (c ^^ y.getD k false)) := by
  decide +kernel

theorem chk_eq : ∀ u < 6, ∀ v < 6, u < v →
    (∀ i < 6, (sig (pairPat 6 u v false) i).Lt 5) ∧
    (∀ i < 5, (sig (eqPerm v) i).Lt 5) ∧
    (∀ z ∈ allRows 5, f1 (inRow 6 (sig (pairPat 6 u v false)) (inRow 5 (sig (eqPerm v)) z)) = w2 z) ∧
    (∀ c : Bool, ∃ y ∈ allRows 5, f1 (inRow 6 (sig (pairPat 6 u v false)) y) ≠ c) ∧
    (∀ k < 5, ∀ c : Bool, ∃ y ∈ allRows 5,
      f1 (inRow 6 (sig (pairPat 6 u v false)) y) ≠ (c ^^ y.getD k false)) := by
  decide +kernel

theorem chk_id : (∀ i < 5, (sig (subPat 5 fun _ => none) i).Lt 5) ∧
    (∀ i < 4, (sig (subPat 4 fun _ => none) i).Lt 4) := by
  decide +kernel

/-! The row sets the CNF writes (`x_S = a`, `x_u ≠ x_v`, `x_u = x_v`) are the substitutions' images. -/

lemma set_eq (n m : ℕ) (σ : ℕ → Rep) (cond : List Bool → Prop) (proj : List Bool → List Bool)
    (hA : ∀ y ∈ allRows m, cond (inRow n σ y))
    (hB : ∀ x ∈ allRows n, cond x → (proj x).length = m ∧ x = inRow n σ (proj x)) :
    {x : List Bool | x.length = n ∧ cond x} = {x | ∃ y : List Bool, y.length = m ∧ x = inRow n σ y} := by
  ext x; constructor
  · rintro ⟨hl, hc⟩; exact ⟨_, (hB x (mem_allRows x n hl) hc).1, (hB x (mem_allRows x n hl) hc).2⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨inRow_length _ _ _, hA y (mem_allRows y m hy)⟩

theorem set_sub1 : ∀ v < 6, ∀ c : Bool,
    (∀ y ∈ allRows 5, (inRow 6 (sig (subPat 6 (fix1 v c))) y).getD v false = c) ∧
    (∀ x ∈ allRows 6, x.getD v false = c →
      (x.eraseIdx v).length = 5 ∧ x = inRow 6 (sig (subPat 6 (fix1 v c))) (x.eraseIdx v)) := by
  decide +kernel

theorem set_sub2 : ∀ u < 6, ∀ v < 6, u < v → ∀ a b : Bool,
    (∀ y ∈ allRows 4, (inRow 6 (sig (subPat 6 (fix2 u v a b))) y).getD u false = a ∧
      (inRow 6 (sig (subPat 6 (fix2 u v a b))) y).getD v false = b) ∧
    (∀ x ∈ allRows 6, (x.getD u false = a ∧ x.getD v false = b) →
      ((x.eraseIdx v).eraseIdx u).length = 4 ∧
      x = inRow 6 (sig (subPat 6 (fix2 u v a b))) ((x.eraseIdx v).eraseIdx u)) := by
  decide +kernel

theorem set_pair : ∀ u < 6, ∀ v < 6, u < v → ∀ neg : Bool,
    (∀ y ∈ allRows 5, (inRow 6 (sig (pairPat 6 u v neg)) y).getD u false =
      (neg ^^ (inRow 6 (sig (pairPat 6 u v neg)) y).getD v false)) ∧
    (∀ x ∈ allRows 6, x.getD u false = (neg ^^ x.getD v false) →
      (x.eraseIdx u).length = 5 ∧ x = inRow 6 (sig (pairPat 6 u v neg)) (x.eraseIdx u)) := by
  decide +kernel

/-- **The `sem` (|S| = 1, 2), `semxor` and `semeq` clauses of the r = 12 run hold in every
circuit for `MOD3^1_6`**, given the certified sizes of the smaller functions as hypotheses. With
`r = gs.length`, each conjunct is `#redundant(T) ≤ r − size`, as `sem_bounds`, `semxor_bound`
and `semeq_bound` in `optimal_circuit.py` pass it. -/
theorem mod3_6_1_sem_bounds
    (h5 : ∀ q < 3, LB 5 (mod3 q) (c5 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q)) (hw : LB 5 w2 10)
    (gs : List Gate) (hne : gs ≠ []) (hgs : ∀ x : List Bool, x.length = 6 → out x gs = mod3 1 x) :
    (∀ v < 6, ∀ c : Bool,
      redCount 6 gs {x | x.length = 6 ∧ x.getD v false = c} + c5 ((4 - c.toNat) % 3) ≤ gs.length) ∧
    (∀ u < 6, ∀ v < 6, u < v → ∀ a b : Bool,
      redCount 6 gs {x | x.length = 6 ∧ (x.getD u false = a ∧ x.getD v false = b)} +
        c4 ((7 - a.toNat - b.toNat) % 3) ≤ gs.length) ∧
    (∀ u < 6, ∀ v < 6, u < v →
      redCount 6 gs {x | x.length = 6 ∧ x.getD u false = (true ^^ x.getD v false)} + c4 0 ≤ gs.length) ∧
    (∀ u < 6, ∀ v < 6, u < v →
      redCount 6 gs {x | x.length = 6 ∧ x.getD u false = (false ^^ x.getD v false)} + 10 ≤ gs.length) := by
  refine ⟨fun v hv c => ?_, fun u hu v hv huv a b => ?_, fun u hu v hv huv => ?_, fun u hu v hv huv => ?_⟩
  · obtain ⟨hσ, hfg, hc, hl⟩ := chk_sub1 v hv c
    obtain ⟨hA, hB⟩ := set_sub1 v hv c
    rw [set_eq 6 5 _ _ _ hA hB]
    exact bound_of_pattern 6 5 _ f1 _ hσ hc hl
      (lb_transfer 5 5 _ chk_id.1 _ _ _ hfg (h5 _ (Nat.mod_lt _ (by omega)))) gs hne hgs
  · obtain ⟨hσ, hfg, hc, hl⟩ := chk_sub2 u hu v hv huv a b
    obtain ⟨hA, hB⟩ := set_sub2 u hu v hv huv a b
    rw [set_eq 6 4 _ _ _ hA hB]
    exact bound_of_pattern 6 4 _ f1 _ hσ hc hl
      (lb_transfer 4 4 _ chk_id.2 _ _ _ hfg (h4 _ (Nat.mod_lt _ (by omega)))) gs hne hgs
  · obtain ⟨hσ, hτ, hfg, hc, hl⟩ := chk_xor u hu v hv huv
    obtain ⟨hA, hB⟩ := set_pair u hu v hv huv true
    rw [set_eq 6 5 _ _ _ hA hB]
    exact bound_of_pattern 6 5 _ f1 _ hσ hc hl
      (lb_transfer 5 4 _ hτ _ _ _ hfg (h4 0 (by omega))) gs hne hgs
  · obtain ⟨hσ, hτ, hfg, hc, hl⟩ := chk_eq u hu v hv huv
    obtain ⟨hA, hB⟩ := set_pair u hu v hv huv false
    rw [set_eq 6 5 _ _ _ hA hB]
    exact bound_of_pattern 6 5 _ f1 _ hσ hc hl (lb_transfer 5 5 _ hτ _ _ _ hfg hw) gs hne hgs

end Mod3SemBounds
