/-
# Symmetry breaking, part 1: swapping adjacent independent gates (for `order`)

`optimal_circuit.encode`'s `order` clause says: if gate i+1 does not read gate i, their input
pairs are in lex order. Its prose proof exchanges two such gates. This file proves the exchange
is harmless, in `CircuitDual`'s bare model.

Proved (axioms: the standard three):
* `swap_nodes`: in `pre ++ [g1, g2] ++ post` (with `p = n + pre.length` the node of `g1`), if `g1`
  reads only nodes `< p` and `g2` does not read node `p`, then listing `g2` before `g1` and
  renaming every read by the transposition `p ↔ p+1` gives a circuit whose node `i` equals the old
  node `sw p i`, for every `i`.
* `swap_out`: so the output is unchanged when `post` is nonempty. (If `post` is empty, the swap
  changes which node is last. In the CNF's model the output is any gate, and under `sym` the
  second-last gate of a minimum circuit is read by the last.)
* `swap_needs_independence`: control. If `g2` reads `g1`, a 2-input instance changes its output.

Part 2, the key-sequence measure, the input transposition and the well-founded argument that a
circuit satisfying `order`, `symin` and the table clause together exists, is `SymCanon.lean`.
-/
import Garden.GateElim

namespace SymBreak
open CircuitDual

/-- Rename every read of a gate by `τ`. -/
def mapG (τ : ℕ → ℕ) (g : Gate) : Gate := ⟨τ g.a, τ g.b, g.op⟩

/-- `l'` is `l` with nodes renamed by `τ`. -/
def R (τ : ℕ → ℕ) (l' l : List Bool) : Prop :=
  l'.length = l.length ∧ ∀ i, l'.getD i false = l.getD (τ i) false

lemma r_step (τ : ℕ → ℕ) (hinv : ∀ i, τ (τ i) = i) (l' l : List Bool) (g : Gate)
    (h : R τ l' l) (hL : τ l.length = l.length)
    (hlt : ∀ i, i < l.length ↔ τ i < l.length) :
    R τ (step l' (mapG τ g)) (step l g) := by
  obtain ⟨hlen, hv⟩ := h
  refine ⟨by simp [step, hlen], fun i => ?_⟩
  simp only [step, mapG]
  rw [getD_append_single, getD_append_single, hlen]; simp only [hv, hinv]
  by_cases hi : i < l.length
  · rw [if_pos hi, if_pos ((hlt i).mp hi)]
  · rw [if_neg hi, if_neg (fun h => hi ((hlt i).mpr h))]
    by_cases he : i = l.length
    · subst he; rw [if_pos rfl, hL, if_pos rfl]
    · rw [if_neg he, if_neg (fun h => he (by rw [← hinv i, h, hL]))]

lemma r_run (τ : ℕ → ℕ) (hinv : ∀ i, τ (τ i) = i) (gs : List Gate) :
    ∀ l' l, R τ l' l → (∀ L, l.length ≤ L → L < l.length + gs.length →
      τ L = L ∧ ∀ i, i < L ↔ τ i < L) →
    R τ (run l' (gs.map (mapG τ))) (run l gs) := by
  induction gs with
  | nil => intro l' l h _; simpa [run] using h
  | cons g gs ih =>
    intro l' l h hτ
    obtain ⟨h1, h2⟩ := hτ l.length le_rfl (by simp)
    have := r_step τ hinv l' l g h h1 h2
    simp only [run, List.map_cons, List.foldl_cons]
    apply ih _ _ this
    intro L hL1 hL2
    simp [step] at hL1 hL2
    exact hτ L (by omega) (by simp; omega)

/-- The transposition of nodes `p` and `p + 1`. -/
def sw (p : ℕ) (i : ℕ) : ℕ := if i = p then p + 1 else if i = p + 1 then p else i

lemma sw_inv (p i : ℕ) : sw p (sw p i) = i := by
  unfold sw; split_ifs <;> omega

lemma sw_of_lt (p i : ℕ) (h : i < p) : sw p i = i := by unfold sw; split_ifs <;> omega
lemma sw_of_gt (p i : ℕ) (h : p + 1 < i) : sw p i = i := by unfold sw; split_ifs <;> omega

lemma getD_two (l : List Bool) (a b : Bool) (i : ℕ) :
    (l ++ [a] ++ [b]).getD i false = if i < l.length then l.getD i false
      else if i = l.length then a else if i = l.length + 1 then b else false := by
  rw [getD_append_single, getD_append_single]; simp only [List.length_append, List.length_singleton]
  split_ifs <;> first | rfl | omega

lemma r_block (p : ℕ) (l' l : List Bool) (g1 g2 : Gate) (h : R (sw p) l' l) (hl : l.length = p)
    (h1a : g1.a < p) (h1b : g1.b < p) (h2a : g2.a ≠ p) (h2b : g2.b ≠ p) :
    R (sw p) (step (step l' (mapG (sw p) g2)) (mapG (sw p) g1)) (step (step l g1) g2) := by
  obtain ⟨hlen, hv⟩ := h
  have agree : ∀ c, c < p → l'.getD c false = l.getD c false := by
    intro c hc; rw [hv, sw_of_lt p c hc]
  have hout : ∀ c, p ≤ c → l.getD c false = false := by
    intro c hc; exact List.getD_eq_default _ _ (by omega)
  -- the two gate values agree
  have e2 : ∀ c, c ≠ p → l'.getD (sw p c) false = (l ++ [g1.op (l.getD g1.a false) (l.getD g1.b false)]).getD c false := by
    intro c hc
    rw [hv, sw_inv, getD_append_single]
    split_ifs with h1 h2
    · rfl
    · omega
    · exact hout c (by omega)
  refine ⟨by simp [step, hlen], fun i => ?_⟩
  simp only [step, mapG]
  rw [getD_two, getD_two, hlen, hl]
  have w1 : g1.op ((l' ++ [g2.op (l'.getD (sw p g2.a) false) (l'.getD (sw p g2.b) false)]).getD (sw p g1.a) false)
      ((l' ++ [g2.op (l'.getD (sw p g2.a) false) (l'.getD (sw p g2.b) false)]).getD (sw p g1.b) false)
      = g1.op (l.getD g1.a false) (l.getD g1.b false) := by
    rw [sw_of_lt p _ h1a, sw_of_lt p _ h1b, List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega), agree _ h1a, agree _ h1b]
  rw [w1, e2 _ h2a, e2 _ h2b]
  by_cases hi : i < p
  · rw [if_pos hi, sw_of_lt p i hi, if_pos hi, agree i hi]
  · rw [if_neg hi]
    by_cases hp : i = p
    · subst hp; simp [sw]
    · by_cases hp1 : i = p + 1
      · subst hp1; simp [sw]
      · rw [if_neg hp, if_neg hp1, sw_of_gt p i (by omega), if_neg (by omega), if_neg hp, if_neg hp1]

/-- **Swapping two adjacent gates when the second does not read the first.** Every node of the
swapped circuit equals the old node it was renamed from. -/
theorem swap_nodes (x : List Bool) (pre post : List Gate) (g1 g2 : Gate) (p : ℕ)
    (hp : p = x.length + pre.length) (h1a : g1.a < p) (h1b : g1.b < p) (h2a : g2.a ≠ p) (h2b : g2.b ≠ p) :
    R (sw p) (run x ((pre ++ [g2, g1] ++ post).map (mapG (sw p)))) (run x (pre ++ [g1, g2] ++ post)) := by
  have split3 : ∀ (A B C : List Gate) (y : List Bool), run y (A ++ B ++ C) = run (run (run y A) B) C := by
    intro A B C y; simp only [run, List.foldl_append]
  rw [List.map_append, List.map_append, split3, split3]
  have s1 : R (sw p) (run x (pre.map (mapG (sw p)))) (run x pre) := by
    apply r_run (sw p) (sw_inv p) pre x x
    · refine ⟨rfl, fun i => ?_⟩
      by_cases hi : i = p ∨ i = p + 1
      · rcases hi with rfl | rfl
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by unfold sw; simp; omega)]
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by unfold sw; simp; omega)]
      · push Not at hi; unfold sw; rw [if_neg hi.1, if_neg hi.2]
    · intro L hL1 hL2
      refine ⟨sw_of_lt p L (by omega), fun i => ?_⟩
      unfold sw; split_ifs <;> omega
  have hlen1 : (run x pre).length = p := by rw [run_length]; omega
  have s2 := r_block p _ _ g1 g2 s1 hlen1 h1a h1b h2a h2b
  have s2' : R (sw p) (run (run x (pre.map (mapG (sw p)))) ([g2, g1].map (mapG (sw p))))
      (run (run x pre) [g1, g2]) := by simpa [run] using s2
  apply r_run (sw p) (sw_inv p) post _ _ s2'
  intro L hL1 _
  have : (run (run x pre) [g1, g2]).length = p + 2 := by rw [run_length, hlen1]; rfl
  refine ⟨sw_of_gt p L (by omega), fun i => ?_⟩
  unfold sw; split_ifs <;> omega

/-- Hence the output is unchanged when some gate follows the pair. -/
theorem swap_out (x : List Bool) (pre post : List Gate) (g1 g2 : Gate)
    (h1a : g1.a < x.length + pre.length) (h1b : g1.b < x.length + pre.length)
    (h2a : g2.a ≠ x.length + pre.length) (h2b : g2.b ≠ x.length + pre.length) (hpost : post ≠ []) :
    out x ((pre ++ [g2, g1] ++ post).map (mapG (sw (x.length + pre.length)))) =
      out x (pre ++ [g1, g2] ++ post) := by
  have h := swap_nodes x pre post g1 g2 _ rfl h1a h1b h2a h2b
  have hp : post.length ≠ 0 := by simpa using hpost
  unfold out
  rw [getLastD_eq_getD, getLastD_eq_getD, h.1, h.2, sw_of_gt]
  rw [run_length]; simp; omega

/-- Control: when the second gate reads the first (`g2.a = p`), the swap can change the output. -/
theorem swap_needs_independence :
    ¬ ∀ x : Fin 2 → Bool,
      out (List.ofFn x) (([] ++ [(⟨2, 0, fun u v => u ^^ v⟩ : Gate), ⟨0, 1, fun u v => u && v⟩] ++
          [(⟨3, 3, fun u _ => u⟩ : Gate)]).map (mapG (sw 2))) =
        out (List.ofFn x) ([] ++ [(⟨0, 1, fun u v => u && v⟩ : Gate), ⟨2, 0, fun u v => u ^^ v⟩] ++
          [(⟨3, 3, fun u _ => u⟩ : Gate)]) := by
  decide

end SymBreak
