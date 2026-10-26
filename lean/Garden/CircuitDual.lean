/-
# Input negation is free in B2 circuits, so size(MOD3^1_6) = size(MOD3^2_6)

Model (deliberately bare). A circuit on `n` inputs is a list of gates. Gate `k` reads two
nodes by index (`0 … n-1` are the inputs, `n + j` is gate `j`) and applies an arbitrary
`Bool → Bool → Bool` table (the full basis B2). Evaluation appends each gate's value to the
list of node values; an out-of-range index reads `false`. The output is the last node.
No well-formedness condition is imposed, and none is needed: the construction below keeps
every gate's wiring (`a`, `b`) unchanged, so it preserves whatever condition one imposes
(acyclic reads, fan-in, a gate count).

Proved:
* `negInputs_nodes`: for every gate list `gs` there is `gs.map (negGate n)`, with the same
  length and wiring, whose every gate node, on input `x`, equals `gs`'s node on input `¬x`.
* `negInputs_out`: hence for nonempty `gs`, the outputs agree: `C'(x) = C(¬x)`.
* `mod3_dual`: `[Σx ≡ 2 mod 3] = [Σ¬x ≡ 1 mod 3]` on 6 bits (by `decide`, 64 cases).
* `mod3_6_size_dual`: a circuit of `s` gates computing `MOD3^1_6` yields one of `s` gates
  computing `MOD3^2_6`, and conversely.

Not proved: anything about what `s` is. The research question (is `size(MOD3^1_6)` 12 or 13?)
is the SAT search in `research/circuits/`; this file only shows that one answer settles both
`r = 1` and `r = 2`.
-/
import Mathlib

namespace CircuitDual

structure Gate where
  a : ℕ
  b : ℕ
  op : Bool → Bool → Bool

/-- Append one gate's value to the node values. -/
def step (vals : List Bool) (g : Gate) : List Bool :=
  vals ++ [g.op (vals.getD g.a false) (vals.getD g.b false)]

/-- All node values: the inputs, then each gate in order. -/
def run (x : List Bool) (gs : List Gate) : List Bool := gs.foldl step x

/-- The circuit's output: its last node. -/
def out (x : List Bool) (gs : List Gate) : Bool := (run x gs).getLastD false

/-- Fold a negation of each input-reading argument into the gate's table. -/
def negGate (n : ℕ) (g : Gate) : Gate :=
  { a := g.a, b := g.b,
    op := fun u v => g.op (if g.a < n then !u else u) (if g.b < n then !v else v) }

/-- `l'` is `l` with its first `n` entries negated. -/
def Rel (n : ℕ) (l' l : List Bool) : Prop :=
  l'.length = l.length ∧ n ≤ l.length ∧
    ∀ i, l'.getD i false = if i < n then !(l.getD i false) else l.getD i false

lemma getD_append_single (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false = if i < l.length then l.getD i false
      else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

lemma rel_step (n : ℕ) (l' l : List Bool) (g : Gate) (h : Rel n l' l) :
    Rel n (step l' (negGate n g)) (step l g) := by
  obtain ⟨hlen, hn, hi⟩ := h
  have arg : ∀ c, (if c < n then !(l'.getD c false) else l'.getD c false) = l.getD c false := by
    intro c; rw [hi c]; split_ifs <;> simp
  refine ⟨by simp [step, hlen], by simp [step]; omega, fun i => ?_⟩
  simp only [step, negGate]
  rw [getD_append_single, getD_append_single, hlen, arg g.a, arg g.b]
  split_ifs <;> first | omega | (try rw [hi i]); simp_all

lemma rel_run (n : ℕ) (gs : List Gate) : ∀ (l' l : List Bool), Rel n l' l →
    Rel n (run l' (gs.map (negGate n))) (run l gs) := by
  induction gs with
  | nil => intro l' l h; simpa [run] using h
  | cons g gs ih =>
    intro l' l h
    simpa [run] using ih _ _ (rel_step n l' l g h)

theorem negInputs_nodes (gs : List Gate) (x : List Bool) :
    let n := x.length
    (gs.map (negGate n)).length = gs.length ∧
    (gs.map (negGate n)).map (fun g => (g.a, g.b)) = gs.map (fun g => (g.a, g.b)) ∧
    ∀ i, n ≤ i → (run x (gs.map (negGate n))).getD i false = (run (x.map (!·)) gs).getD i false := by
  intro n
  refine ⟨by simp, by simp [negGate], fun i hi => ?_⟩
  have h0 : Rel n x (x.map (!·)) := ⟨by simp, by simp [n], fun j => by
    split_ifs with hj
    · have hj' : j < x.length := hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]⟩
  rw [(rel_run n gs _ _ h0).2.2 i, if_neg (by omega)]

lemma run_length (x : List Bool) (gs : List Gate) : (run x gs).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => simp [run, step] at ih ⊢; rw [ih]; simp; omega

lemma getLastD_eq_getD (l : List Bool) : l.getLastD false = l.getD (l.length - 1) false := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem negInputs_out (gs : List Gate) (hgs : gs ≠ []) (x : List Bool) :
    out x (gs.map (negGate x.length)) = out (x.map (!·)) gs := by
  obtain ⟨-, -, h⟩ := negInputs_nodes gs x
  have hne : gs.length ≠ 0 := by simpa using hgs
  unfold out
  rw [getLastD_eq_getD, getLastD_eq_getD, run_length, run_length, h _ (by simp; omega)]
  simp

/-- `MOD3^r_n` on a bit list. -/
def mod3 (r : ℕ) (x : List Bool) : Bool := decide ((x.map Bool.toNat).sum % 3 = r)

theorem mod3_dual : ∀ x : Fin 6 → Bool, mod3 2 (List.ofFn x) = mod3 1 ((List.ofFn x).map (!·)) := by
  decide

/-- A circuit of `gs.length` gates computes `MOD3^r_6` (gates nonempty: the output is a gate). -/
def Computes (r : ℕ) (gs : List Gate) : Prop :=
  gs ≠ [] ∧ ∀ x : Fin 6 → Bool, out (List.ofFn x) gs = mod3 r (List.ofFn x)

theorem mod3_6_size_dual (gs : List Gate) :
    (Computes 1 gs → ∃ gs', gs'.length = gs.length ∧ Computes 2 gs') ∧
    (Computes 2 gs → ∃ gs', gs'.length = gs.length ∧ Computes 1 gs') := by
  have neg6 : ∀ x : Fin 6 → Bool, (List.ofFn x).map (!·) = List.ofFn (fun i => !x i) := by
    intro x; simp
  refine ⟨fun ⟨hne, hc⟩ => ⟨gs.map (negGate 6), by simp, by simpa using hne, fun x => ?_⟩,
          fun ⟨hne, hc⟩ => ⟨gs.map (negGate 6), by simp, by simpa using hne, fun x => ?_⟩⟩
  · have := negInputs_out gs hne (List.ofFn x)
    simp only [List.length_ofFn] at this
    rw [this, neg6, hc, ← neg6, mod3_dual]
  · have := negInputs_out gs hne (List.ofFn x)
    simp only [List.length_ofFn] at this
    rw [this, neg6, hc, ← neg6]
    have := mod3_dual (fun i => !x i)
    rw [neg6] at this; simp only [Bool.not_not] at this
    rw [neg6]; exact this

end CircuitDual
