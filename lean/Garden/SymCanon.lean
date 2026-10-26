/-
# Symmetry breaking, part 2: the canonical form behind `order`, `symin`, `first01` and the table clause

`research/circuits/optimal_circuit.encode` and `cubes.py` add four symmetry-breaking constraints
whose soundness was argued in prose (the `symin` paragraph of `encode`'s docstring): among all
relabelings of the inputs and all topological listings of a circuit, take one whose key sequence
`(pair(i), rank(table(i)))` is lex-least. This file proves that argument in `CircuitDual`'s
model, restricted to the shape the CNF uses.

The CNF's circuits (`Shaped`, `Normal`, `outAt`): gate `i` is node `n + i`; it reads a sorted
pair `a < b` of earlier nodes; its table is normal (`0` on `00`); the output is any gate `o`,
xor a bit `neg`. The constraints, stated as the CNF's clauses state them:
* `Order`: if gate `i+1` does not read gate `i`, then `pair(i) ≤ pair(i+1)` lexicographically;
* `SymInOrd S`: for inputs `u < v` both in `S`, if a gate reads `x_v`, some gate at or before
  it reads `x_u` (`encode`'s `symin` is this for `S` = all inputs and `v = u + 1`; `symvars` is
  this for `S` = the listed inputs);
* `TableOK S`: if the first gate reads two inputs of `S`, its table is not `(f01, f10, f11) =
  (1, 0, 0)` (`cubes.py`'s base clause; `symvars`' table clause);
* `first01` is a corollary of `SymInOrd` when `S` is all inputs (`first01_of_symin`).

Proved (axioms: the standard three):
* `canonical`: let `f` be invariant under swapping any two inputs in `S`. Every shaped, normal
  circuit computing `f` has a shaped, normal circuit **of the same length** computing `f` that
  satisfies `Order`, `SymInOrd S` and `TableOK S` together. The proof is a well-founded descent
  on the key sequence, read as a base-`M` number: a violated `Order` swaps the two gates
  (`SymBreak.swap_nodes`), a violated `SymInOrd` or `TableOK` swaps two inputs (`tr_nodes`), and
  each step keeps every key before the first change and lowers the key there.
* `mod3_6_canonical`: the instance the r = 12 run uses, `MOD3^1_6` with `S` = all six inputs,
  including `first01`.
* `c13_satisfies`: the 13-gate circuit decoded from the r = 13 SAT model satisfies these Lean
  definitions (`decide`). The CNF and the definitions agree on at least that model.

Controls:
* `canonical_needs_symmetry`: without the symmetry hypothesis the conclusion is false (`¬x0 ∧ x1`
  on two inputs: its only 1-gate circuits have table `(1, 0, 0)`).
* `order_detects`, `symin_detects`, `table_detects`: a small circuit violating each constraint
  is rejected by `decide`, so the definitions are not vacuous.

Not proved here: that `encode`'s clauses say exactly these definitions (read by eye; the
`c13` check is evidence, not proof); the move from an arbitrary B2 circuit to a normal one with
an output bit; `sym`'s no-dead-gate half and `allin`.
-/
import Garden.SymBreak
import Garden.Mod3SemBounds
import Garden.Mod3Upper

namespace SymCanon
open CircuitDual SymBreak

/-! ### The CNF's circuit shape -/

/-- Gate `i` of the list (node `m + i`) reads a sorted pair of earlier nodes. -/
def ShapedFrom : ℕ → List Gate → Prop
  | _, [] => True
  | m, g :: gs => (g.a < g.b ∧ g.b < m) ∧ ShapedFrom (m + 1) gs

/-- The CNF's shape on `n` inputs. `shaped_iff` gives the indexed form. -/
def Shaped (n : ℕ) (gs : List Gate) : Prop := ShapedFrom n gs

/-- Every table is normal: `0` on `00`. -/
def Normal (gs : List Gate) : Prop := ∀ g ∈ gs, g.op false false = false

instance (gs : List Gate) : Decidable (Normal gs) := inferInstanceAs (Decidable (∀ g ∈ gs, _))

/-- The output: node `o`, xor `neg`. -/
def outAt (x : List Bool) (gs : List Gate) (o : ℕ) (neg : Bool) : Bool :=
  neg ^^ (run x gs).getD o false

def ComputesAt (n : ℕ) (f : List Bool → Bool) (gs : List Gate) (o : ℕ) (neg : Bool) : Prop :=
  ∀ x : List Bool, x.length = n → outAt x gs o neg = f x

lemma shapedFrom_iff : ∀ (m : ℕ) (gs : List Gate),
    ShapedFrom m gs ↔ ∀ i (h : i < gs.length), gs[i].a < gs[i].b ∧ gs[i].b < m + i
  | m, [] => by simp [ShapedFrom]
  | m, g :: gs => by
    rw [ShapedFrom, shapedFrom_iff (m + 1) gs]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ j =>
        have := h j (by simpa using hi)
        simp only [List.getElem_cons_succ]; omega
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this; omega

theorem shaped_iff (n : ℕ) (gs : List Gate) :
    Shaped n gs ↔ ∀ i (h : i < gs.length), gs[i].a < gs[i].b ∧ gs[i].b < n + i :=
  shapedFrom_iff n gs

lemma shapedFrom_append : ∀ (m : ℕ) (A B : List Gate),
    ShapedFrom m (A ++ B) ↔ ShapedFrom m A ∧ ShapedFrom (m + A.length) B
  | m, [], B => by simp [ShapedFrom]
  | m, g :: A, B => by
    simp only [List.cons_append, ShapedFrom, shapedFrom_append (m + 1) A B, List.length_cons]
    rw [show m + 1 + A.length = m + (A.length + 1) by omega]; tauto

lemma shapedFrom_bound : ∀ (m : ℕ) (gs : List Gate), ShapedFrom m gs →
    ∀ g ∈ gs, g.a < g.b ∧ g.b < m + gs.length
  | m, [], _ => by simp
  | m, g :: gs, ⟨h0, h⟩ => by
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hm
    · simp; omega
    · have := shapedFrom_bound (m + 1) gs h g' hm; simp; omega

/-! ### The constraints -/

/-- Gate `g` reads node `c`. -/
def Reads (g : Gate) (c : ℕ) : Prop := g.a = c ∨ g.b = c

instance (g : Gate) (c : ℕ) : Decidable (Reads g c) := inferInstanceAs (Decidable (_ ∨ _))

/-- `pair(g) < pair(h)` lexicographically. -/
def PairLt (g h : Gate) : Prop := g.a < h.a ∨ (g.a = h.a ∧ g.b < h.b)

instance (g h : Gate) : Decidable (PairLt g h) := inferInstanceAs (Decidable (_ ∨ _))

/-- The table `(f01, f10, f11) = (1, 0, 0)`, i.e. `¬x_a ∧ x_b`. -/
def T100 (g : Gate) : Prop := g.op false true = true ∧ g.op true false = false ∧ g.op true true = false

instance (g : Gate) : Decidable (T100 g) := inferInstanceAs (Decidable (_ ∧ _))

/-- `encode`'s `order`: if gate `i+1` does not read gate `i` (node `n + i`), then
`pair(i) ≤ pair(i+1)`. -/
def Order (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (h : i + 1 < gs.length), ¬ Reads gs[i + 1] (n + i) → ¬ PairLt gs[i + 1] gs[i]

/-- `encode`'s `symin` (and `symvars`), for all `u < v` in `S`: if gate `i` reads `x_v`, one of
gates `0 … i` reads `x_u`. -/
def SymInOrd (S : ℕ → Prop) (gs : List Gate) : Prop :=
  ∀ u v, S u → S v → u < v → ∀ i (h : i < gs.length), Reads gs[i] v →
    ∃ g ∈ gs.take (i + 1), Reads g u

/-- `cubes.py`'s table clause (and `symvars`'): if the first gate reads two inputs of `S`, its
table is not `(1, 0, 0)`. -/
def TableOK (S : ℕ → Prop) (gs : List Gate) : Prop :=
  ∀ h : 0 < gs.length, S gs[0].a → S gs[0].b → ¬ T100 gs[0]

/-! ### Re-sorting a pair, and renaming reads -/

/-- Put a gate's pair in order, swapping its table's arguments if needed. -/
def sortG (g : Gate) : Gate := if g.b < g.a then ⟨g.b, g.a, fun u v => g.op v u⟩ else g

lemma step_sortG (l : List Bool) (g : Gate) : step l (sortG g) = step l g := by
  unfold sortG; split_ifs <;> simp [step]

lemma run_map_sortG (x : List Bool) (gs : List Gate) : run x (gs.map sortG) = run x gs := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, List.map_cons, List.foldl_cons] at ih ⊢
    rw [step_sortG]; exact ih _

/-- Rename a gate's reads by `τ`, then re-sort. -/
def ren (τ : ℕ → ℕ) (g : Gate) : Gate := sortG (mapG τ g)

lemma ren_id (τ : ℕ → ℕ) (g : Gate) (ha : τ g.a = g.a) (hb : τ g.b = g.b) (hab : g.a < g.b) :
    ren τ g = g := by
  unfold ren sortG mapG; dsimp only; rw [ha, hb, if_neg (by omega)]

lemma ren_normal (τ : ℕ → ℕ) (g : Gate) (h : g.op false false = false) :
    (ren τ g).op false false = false := by
  unfold ren sortG mapG; split_ifs <;> simpa using h

lemma ren_shape (τ : ℕ → ℕ) (g : Gate) (m : ℕ) (hne : τ g.a ≠ τ g.b) (ha : τ g.a < m) (hb : τ g.b < m) :
    (ren τ g).a < (ren τ g).b ∧ (ren τ g).b < m := by
  unfold ren sortG mapG; split_ifs <;> (try dsimp only at *) <;> omega

lemma shapedFrom_map (τ : ℕ → ℕ) (hinj : ∀ a b, τ a = τ b → a = b) :
    ∀ (m : ℕ) (gs : List Gate), (∀ m' ≥ m, ∀ c < m', τ c < m') →
      ShapedFrom m gs → ShapedFrom m (gs.map (ren τ))
  | _, [], _, _ => trivial
  | m, g :: gs, hτ, ⟨⟨hab, hb⟩, h⟩ => by
    refine ⟨ren_shape τ g m (fun e => by have := hinj _ _ e; omega) (hτ m le_rfl _ (by omega))
      (hτ m le_rfl _ hb), ?_⟩
    exact shapedFrom_map τ hinj (m + 1) gs (fun m' hm' => hτ m' (by omega)) h

lemma normal_map (τ : ℕ → ℕ) (gs : List Gate) (h : Normal gs) : Normal (gs.map (ren τ)) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  exact ren_normal τ g0 (h g0 hg0)

/-! ### Swapping two inputs -/

/-- The transposition of `u` and `v`. -/
def tr (u v i : ℕ) : ℕ := if i = u then v else if i = v then u else i

lemma tr_inv (u v i : ℕ) : tr u v (tr u v i) = i := by unfold tr; split_ifs <;> omega

/-- The input row with `x_u` and `x_v` exchanged. -/
def swapIn (u v : ℕ) (x : List Bool) : List Bool :=
  (List.range x.length).map fun i => x.getD (tr u v i) false

lemma swapIn_length (u v : ℕ) (x : List Bool) : (swapIn u v x).length = x.length := by
  simp [swapIn]

lemma swapIn_getD (u v : ℕ) (x : List Bool) (i : ℕ) :
    (swapIn u v x).getD i false = if i < x.length then x.getD (tr u v i) false else false := by
  unfold swapIn; split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_default]; simp; omega

/-- `f` is unchanged by swapping any two inputs in `S`. -/
def SymOn (n : ℕ) (S : ℕ → Prop) (f : List Bool → Bool) : Prop :=
  ∀ u v, S u → S v → ∀ x : List Bool, x.length = n → f (swapIn u v x) = f x

/-- Renaming the reads by the input transposition `(u v)` gives a circuit whose node `i` on `x`
is the old node `tr u v i` on the swapped row. -/
theorem tr_nodes (n u v : ℕ) (hu : u < n) (hv : v < n) (x : List Bool) (hx : x.length = n)
    (gs : List Gate) : R (tr u v) (run x (gs.map (ren (tr u v)))) (run (swapIn u v x) gs) := by
  have e : gs.map (ren (tr u v)) = (gs.map (mapG (tr u v))).map sortG := by
    simp only [List.map_map]; rfl
  rw [e, run_map_sortG]
  apply r_run (tr u v) (tr_inv u v) gs x (swapIn u v x)
  · refine ⟨by rw [swapIn_length], fun i => ?_⟩
    rw [swapIn_getD]
    by_cases hi : i < n
    · have : tr u v i < x.length := by unfold tr; split_ifs <;> omega
      rw [if_pos this, tr_inv]
    · have : tr u v i = i := by unfold tr; split_ifs <;> omega
      rw [this, if_neg (by omega), List.getD_eq_default _ _ (by omega)]
  · intro L hL _
    rw [swapIn_length] at hL
    exact ⟨by unfold tr; split_ifs <;> omega, fun i => by unfold tr; split_ifs <;> omega⟩

theorem tr_computes (n : ℕ) (S : ℕ → Prop) (hS : ∀ u, S u → u < n) (f : List Bool → Bool)
    (hf : SymOn n S f) (u v : ℕ) (hu : S u) (hv : S v) (gs : List Gate) (o : ℕ) (neg : Bool)
    (ho : n ≤ o) (hc : ComputesAt n f gs o neg) :
    ComputesAt n f (gs.map (ren (tr u v))) o neg := by
  intro x hx
  have hu' := hS u hu; have hv' := hS v hv
  have h := (tr_nodes n u v hu' hv' x hx gs).2 o
  have ho' : tr u v o = o := by unfold tr; split_ifs <;> omega
  unfold outAt; rw [h, ho']
  have := hc (swapIn u v x) (by rw [swapIn_length, hx])
  unfold outAt at this; rw [this, hf u v hu hv x hx]

lemma tr_shaped (n u v : ℕ) (hu : u < n) (hv : v < n) (gs : List Gate) (h : Shaped n gs) :
    Shaped n (gs.map (ren (tr u v))) :=
  shapedFrom_map (tr u v) (fun a b e => by rw [← tr_inv u v a, e, tr_inv]) n gs
    (fun m' hm' c hc => by unfold tr; split_ifs <;> omega) h

/-- Swapping `x_u` and `x_v` at a gate that reads `x_v` and not `x_u`, with `u < v`, lowers its
pair. -/
lemma ren_tr_pairLt (u v : ℕ) (g : Gate) (hab : g.a < g.b) (huv : u < v) (hv : Reads g v)
    (hu : ¬ Reads g u) : PairLt (ren (tr u v) g) g := by
  unfold Reads at hv hu; push Not at hu
  unfold ren sortG mapG PairLt tr
  rcases hv with h | h <;> split_ifs <;> (try dsimp only at *) <;> omega

/-- Swapping the two inputs of a `(1, 0, 0)` gate keeps its pair and gives table `(0, 1, 0)`. -/
lemma ren_tr_table (g : Gate) (hab : g.a < g.b) (hT : T100 g) :
    (ren (tr g.a g.b) g).a = g.a ∧ (ren (tr g.a g.b) g).b = g.b ∧ ¬ T100 (ren (tr g.a g.b) g) := by
  have h1 : tr g.a g.b g.a = g.b := by unfold tr; simp
  have h2 : tr g.a g.b g.b = g.a := by unfold tr; rw [if_neg (by omega), if_pos rfl]
  unfold ren mapG; simp only [h1, h2]
  unfold sortG; rw [if_pos hab]
  refine ⟨rfl, rfl, fun ⟨h, _⟩ => ?_⟩
  unfold T100 at hT; simp only at h; rw [hT.2.1] at h; exact Bool.false_ne_true h

/-! ### The key sequence as a number -/

/-- A gate's key: its pair, then whether its table is `(1, 0, 0)` (which ranks last). -/
def key (N : ℕ) (g : Gate) : ℕ := (g.a * N + g.b) * 2 + (if T100 g then 1 else 0)

lemma key_lt (N : ℕ) (g : Gate) (ha : g.a < N) (hb : g.b < N) : key N g < 2 * (N * N) := by
  have : (g.a + 1) * N ≤ N * N := Nat.mul_le_mul_right _ ha
  rw [add_mul, one_mul] at this
  unfold key; split_ifs <;> omega

lemma key_lt_of_pairLt (N : ℕ) (g g' : Gate) (hb' : g'.b < N) (h : PairLt g' g) :
    key N g' < key N g := by
  unfold key
  rcases h with h | ⟨h1, h2⟩
  · have : (g'.a + 1) * N ≤ g.a * N := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at this
    split_ifs <;> omega
  · rw [h1]; split_ifs <;> omega

/-- A list of digits, big-endian, in base `M`. -/
def enc (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * M ^ ds.length + enc M ds

lemma enc_lt (M : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, d < M) → enc M ds < M ^ ds.length
  | [], _ => by simp [enc]
  | d :: ds, h => by
    have h1 := enc_lt M ds (fun e he => h e (by simp [he]))
    have h2 : d + 1 ≤ M := h d (by simp)
    have : (d + 1) * M ^ ds.length ≤ M * M ^ ds.length := Nat.mul_le_mul_right _ h2
    rw [add_mul, one_mul] at this
    simp only [enc, List.length_cons, pow_succ]
    rw [mul_comm (M ^ ds.length) M]; omega

/-- Lexicographic order: a smaller digit after a common prefix gives a smaller number. -/
lemma enc_lex (M : ℕ) (d' d : ℕ) (R' R : List ℕ) (hlen : R'.length = R.length)
    (hR' : ∀ e ∈ R', e < M) (hd : d' < d) : ∀ P : List ℕ, enc M (P ++ d' :: R') < enc M (P ++ d :: R)
  | [] => by
    have h1 := enc_lt M R' hR'
    have : (d' + 1) * M ^ R.length ≤ d * M ^ R.length := Nat.mul_le_mul_right _ hd
    rw [add_mul, one_mul] at this
    simp only [List.nil_append, enc, hlen] at h1 ⊢; omega
  | p :: P => by
    have := enc_lex M d' d R' R hlen hR' hd P
    simp only [List.cons_append, enc, List.length_append, List.length_cons, hlen]; omega

/-- The measure: the key sequence in base `2 N²`. -/
def μ (N : ℕ) (gs : List Gate) : ℕ := enc (2 * (N * N)) (gs.map (key N))

lemma mu_lt (N : ℕ) (A B B' : List Gate) (g g' : Gate) (hlen : B'.length = B.length)
    (hB' : ∀ h ∈ B', h.a < N ∧ h.b < N) (hk : key N g' < key N g) :
    μ N (A ++ g' :: B') < μ N (A ++ g :: B) := by
  unfold μ; simp only [List.map_append, List.map_cons]
  apply enc_lex _ _ _ _ _ (by simpa using hlen) _ hk
  intro e he
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp he
  exact key_lt N h (hB' h hh).1 (hB' h hh).2

/-! ### Swapping two adjacent gates (`order`) -/

/-- If gate `g2` does not read gate `g1` (node `p = n + pre.length`), listing `g2` first and
renaming later reads by `p ↔ p + 1` gives a shaped, normal circuit computing the same function,
with output `sw p o`. -/
theorem swap_step (n : ℕ) (f : List Bool → Bool) (neg : Bool) (pre post : List Gate) (g1 g2 : Gate)
    (o : ℕ) (hsh : Shaped n (pre ++ g1 :: g2 :: post)) (hnorm : Normal (pre ++ g1 :: g2 :: post))
    (ho1 : n ≤ o) (ho2 : o < n + (pre.length + 2 + post.length))
    (hc : ComputesAt n f (pre ++ g1 :: g2 :: post) o neg) (hind : ¬ Reads g2 (n + pre.length)) :
    Shaped n (pre ++ g2 :: g1 :: post.map (ren (sw (n + pre.length)))) ∧
    Normal (pre ++ g2 :: g1 :: post.map (ren (sw (n + pre.length)))) ∧
    n ≤ sw (n + pre.length) o ∧ sw (n + pre.length) o < n + (pre.length + 2 + post.length) ∧
    ComputesAt n f (pre ++ g2 :: g1 :: post.map (ren (sw (n + pre.length))))
      (sw (n + pre.length) o) neg := by
  set p := n + pre.length with hp
  unfold Shaped at hsh
  rw [shapedFrom_append] at hsh
  simp only [ShapedFrom] at hsh
  obtain ⟨hpre, ⟨h1ab, h1b⟩, ⟨h2ab, h2b⟩, hpost⟩ := hsh
  unfold Reads at hind; push Not at hind
  have h2b' : g2.b < p := by omega
  have hpreB := shapedFrom_bound n pre hpre
  have hfix : ∀ g ∈ pre, ren (sw p) g = g := fun g hg => by
    obtain ⟨hab, hb⟩ := hpreB g hg
    exact ren_id _ g (sw_of_lt p _ (by omega)) (sw_of_lt p _ (by omega)) hab
  have hfix1 : ren (sw p) g1 = g1 := ren_id _ g1 (sw_of_lt p _ (by omega)) (sw_of_lt p _ h1b) h1ab
  have hfix2 : ren (sw p) g2 = g2 := ren_id _ g2 (sw_of_lt p _ (by omega)) (sw_of_lt p _ h2b') h2ab
  have hlist : (pre ++ [g2, g1] ++ post).map (ren (sw p)) =
      pre ++ g2 :: g1 :: post.map (ren (sw p)) := by
    simp only [List.map_append, List.map_cons, List.map_nil, hfix1, hfix2]
    rw [List.map_congr_left hfix, List.map_id']; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Shaped; rw [shapedFrom_append]; simp only [ShapedFrom]
    refine ⟨hpre, ⟨h2ab, h2b'⟩, ⟨h1ab, by omega⟩, ?_⟩
    apply shapedFrom_map (sw p) (fun a b e => by rw [← sw_inv p a, e, sw_inv]) _ post _ hpost
    intro m' hm' c hc; unfold sw; split_ifs <;> omega
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hg
    rcases hg with hg | rfl | rfl | ⟨g0, hg0, rfl⟩
    · exact hnorm g (by simp [hg])
    · exact hnorm g (by simp)
    · exact hnorm g (by simp)
    · exact ren_normal _ g0 (hnorm g0 (by simp [hg0]))
  · unfold sw; split_ifs <;> omega
  · unfold sw; split_ifs <;> omega
  · intro x hx
    have hR := swap_nodes x pre post g1 g2 p (by rw [hx]) (by omega) h1b hind.1 hind.2
    have hrun : run x (pre ++ g2 :: g1 :: post.map (ren (sw p))) =
        run x ((pre ++ [g2, g1] ++ post).map (mapG (sw p))) := by
      rw [← hlist, ← run_map_sortG x ((pre ++ [g2, g1] ++ post).map (mapG (sw p))), List.map_map]
      rfl
    have e1 : pre ++ [g1, g2] ++ post = pre ++ g1 :: g2 :: post := by simp
    have hco := hc x hx
    unfold outAt at hco ⊢
    rw [hrun, hR.2, sw_inv, e1]; exact hco

/-! ### The descent -/

/-- **The canonical form.** Let `f` (on `n` inputs) be unchanged by swapping any two inputs of
`S`. Every shaped, normal circuit computing `f` with output `(o, neg)` has a shaped, normal
circuit of the same length computing `f` that satisfies `Order`, `SymInOrd S` and `TableOK S`. -/
theorem canonical (n : ℕ) (S : ℕ → Prop) (hS : ∀ u, S u → u < n) (f : List Bool → Bool)
    (hf : SymOn n S f) (neg : Bool) (gs : List Gate) (o : ℕ) (hsh : Shaped n gs)
    (hnorm : Normal gs) (ho1 : n ≤ o) (ho2 : o < n + gs.length) (hc : ComputesAt n f gs o neg) :
    ∃ gs' o', gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧ n ≤ o' ∧
      o' < n + gs'.length ∧ ComputesAt n f gs' o' neg ∧ Order n gs' ∧ SymInOrd S gs' ∧
      TableOK S gs' := by
  classical
  obtain ⟨L, hL⟩ : ∃ L, gs.length = L := ⟨_, rfl⟩
  suffices H : ∀ k, ∀ gs : List Gate, ∀ o, gs.length = L → μ (n + L) gs = k → Shaped n gs →
      Normal gs → n ≤ o → o < n + gs.length → ComputesAt n f gs o neg →
      ∃ gs' o', gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧ n ≤ o' ∧
        o' < n + gs'.length ∧ ComputesAt n f gs' o' neg ∧ Order n gs' ∧ SymInOrd S gs' ∧
        TableOK S gs' from H _ gs o hL rfl hsh hnorm ho1 ho2 hc
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro gs o hL hk hsh hnorm ho1 ho2 hc
  have bnd : ∀ gs'' : List Gate, Shaped n gs'' → gs''.length = L →
      ∀ h ∈ gs'', h.a < n + L ∧ h.b < n + L := by
    intro gs'' hs hl h hh
    have := shapedFrom_bound n gs'' hs h hh; rw [hl] at this; omega
  have descend : ∀ gs'' o'', gs''.length = L → Shaped n gs'' → Normal gs'' → n ≤ o'' →
      o'' < n + gs''.length → ComputesAt n f gs'' o'' neg → μ (n + L) gs'' < k →
      ∃ gs' o', gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧ n ≤ o' ∧
        o' < n + gs'.length ∧ ComputesAt n f gs' o' neg ∧ Order n gs' ∧ SymInOrd S gs' ∧
        TableOK S gs' := by
    intro gs'' o'' hl hs hn h1 h2 hc' hlt
    obtain ⟨gs', o', e, r⟩ := ih _ hlt gs'' o'' hl rfl hs hn h1 h2 hc'
    exact ⟨gs', o', by rw [e, hl, hL], r⟩
  by_cases hO : Order n gs
  · by_cases hI : SymInOrd S gs
    · by_cases hT : TableOK S gs
      · exact ⟨gs, o, rfl, hsh, hnorm, ho1, ho2, hc, hO, hI, hT⟩
      · -- the first gate is `(1, 0, 0)` on two inputs of `S`: swap those inputs
        unfold TableOK at hT; push Not at hT
        obtain ⟨h0, hSa, hSb, hT100⟩ := hT
        cases gs with
        | nil => simp at h0
        | cons g B =>
          simp only [List.getElem_cons_zero] at hSa hSb hT100
          have hab : g.a < g.b := hsh.1.1
          have ha := hS _ hSa; have hb := hS _ hSb
          obtain ⟨e1, e2, hT'⟩ := ren_tr_table g hab hT100
          apply descend ((g :: B).map (ren (tr g.a g.b))) o (by simpa using hL)
            (tr_shaped n _ _ ha hb _ hsh) (normal_map _ _ hnorm) ho1 (by simpa using ho2)
            (tr_computes n S hS f hf _ _ hSa hSb _ o neg ho1 hc)
          rw [← hk, List.map_cons]
          have hs' := tr_shaped n _ _ ha hb _ hsh
          have hl' : ((g :: B).map (ren (tr g.a g.b))).length = L := by simpa using hL
          apply mu_lt (n + L) [] B (B.map (ren (tr g.a g.b))) g _ (by simp)
          · intro h hh
            exact bnd _ hs' hl' h (by simp [List.map_cons] at hh ⊢; exact Or.inr hh)
          · unfold key; rw [e1, e2, if_neg hT', if_pos hT100]; omega
    · -- `x_v` is read before `x_u`, `u < v`: swap them at the first gate reading `x_v`
      unfold SymInOrd at hI; push Not at hI
      obtain ⟨u, v, hSu, hSv, huv, i, hi, hv, hnu⟩ := hI
      have hu' := hS u hSu; have hv' := hS v hSv
      have hex : ∃ i, ∃ h : i < gs.length, Reads gs[i] v := ⟨i, hi, hv⟩
      obtain ⟨hi0, hv0⟩ := Nat.find_spec hex
      have hle : Nat.find hex ≤ i := Nat.find_min' hex ⟨hi, hv⟩
      have hmin : ∀ j < Nat.find hex, ¬ ∃ h : j < gs.length, Reads gs[j] v :=
        fun j hj => Nat.find_min hex hj
      obtain ⟨A, g, B, rfl, hA, hgv, hgu⟩ : ∃ A g B, gs = A ++ g :: B ∧
          (∀ h ∈ A, ¬ Reads h u ∧ ¬ Reads h v) ∧ Reads g v ∧ ¬ Reads g u := by
        refine ⟨gs.take (Nat.find hex), gs[Nat.find hex], gs.drop (Nat.find hex + 1), ?_, ?_, hv0, ?_⟩
        · conv_lhs => rw [← List.take_append_drop (Nat.find hex) gs]
          rw [List.drop_eq_getElem_cons hi0]
        · intro h hh
          obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hh
          have hj1 : j < Nat.find hex := by omega
          refine ⟨fun hr => hnu _ (List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩) hr,
            fun hr => hmin j hj1 ⟨by omega, hr⟩⟩
        · exact fun hr => hnu _ (List.mem_take_iff_getElem.mpr ⟨Nat.find hex, by omega, rfl⟩) hr
      have hsA := shapedFrom_bound n _ hsh
      have hfixA : ∀ h ∈ A, ren (tr u v) h = h := by
        intro h hh
        obtain ⟨hr1, hr2⟩ := hA h hh
        unfold Reads at hr1 hr2; push Not at hr1 hr2
        exact ren_id _ h (by unfold tr; rw [if_neg hr1.1, if_neg hr2.1])
          (by unfold tr; rw [if_neg hr1.2, if_neg hr2.2]) (hsA h (by simp [hh])).1
      have hmap : (A ++ g :: B).map (ren (tr u v)) = A ++ ren (tr u v) g :: B.map (ren (tr u v)) := by
        rw [List.map_append, List.map_cons, List.map_congr_left hfixA, List.map_id']
      have hs' := tr_shaped n u v hu' hv' _ hsh
      have hl' : ((A ++ g :: B).map (ren (tr u v))).length = L := by simpa using hL
      apply descend _ o hl' hs' (normal_map _ _ hnorm) ho1 (by simpa using ho2)
        (tr_computes n S hS f hf u v hSu hSv _ o neg ho1 hc)
      rw [← hk, hmap]
      rw [hmap] at hs' hl'
      apply mu_lt (n + L) A B _ g _ (by simp)
      · intro h hh; exact bnd _ hs' hl' h (by simp [hh])
      · apply key_lt_of_pairLt _ _ _ (bnd _ hs' hl' _ (by simp)).2
        exact ren_tr_pairLt u v g (hsA g (by simp)).1 huv hgv hgu
  · -- gate `i + 1` does not read gate `i` and has a smaller pair: swap them
    unfold Order at hO; push Not at hO
    obtain ⟨i, hi, hnr, hlt⟩ := hO
    obtain ⟨pre, g1, g2, post, rfl, hpl, hnr', hlt'⟩ : ∃ pre g1 g2 post,
        gs = pre ++ g1 :: g2 :: post ∧ pre.length = i ∧ ¬ Reads g2 (n + i) ∧ PairLt g2 g1 := by
      refine ⟨gs.take i, gs[i], gs[i + 1], gs.drop (i + 1 + 1), ?_, by simp; omega, hnr, hlt⟩
      conv_lhs => rw [← List.take_append_drop i gs]
      rw [List.drop_eq_getElem_cons (show i < gs.length by omega),
        List.drop_eq_getElem_cons (show i + 1 < gs.length by omega)]
    subst hpl
    simp only [List.length_append, List.length_cons] at ho2 hL
    obtain ⟨hs', hn', h1, h2, hc'⟩ := swap_step n f neg pre post g1 g2 o hsh hnorm ho1
      (by omega) hc hnr'
    have hl' : (pre ++ g2 :: g1 :: post.map (ren (sw (n + pre.length)))).length = L := by
      simp; omega
    apply descend _ _ hl' hs' hn' h1 (by simp; omega) hc'
    rw [← hk]
    apply mu_lt (n + L) pre (g2 :: post) (g1 :: post.map (ren (sw (n + pre.length)))) g1 g2
      (by simp)
    · intro h hh; exact bnd _ hs' hl' h (by simp at hh ⊢; tauto)
    · exact key_lt_of_pairLt _ _ _ (bnd _ hs' hl' g2 (by simp)).2 hlt'

/-! ### Corollaries: `first01`, and the two instances the runs used -/

/-- With `S` = all inputs, `SymInOrd` forces the first gate to read `(x0, x1)`: if it read
`x_a` with `a > 0`, then `x_a` would be read before `x0`. -/
theorem first01_of_symin (n : ℕ) (gs : List Gate) (hsh : Shaped n gs) (hI : SymInOrd (· < n) gs)
    (h : 0 < gs.length) : gs[0].a = 0 ∧ gs[0].b = 1 := by
  have hs := (shaped_iff n gs).mp hsh 0 h
  simp only [Nat.add_zero] at hs
  have first : ∀ g ∈ gs.take 1, g = gs[0] := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hg
    have : j = 0 := by omega
    subst this; rfl
  have ha : gs[0].a = 0 := by
    by_contra ha
    obtain ⟨g, hg, hr⟩ := hI 0 gs[0].a (by omega) (by omega) (by omega) 0 h (Or.inl rfl)
    rw [first g hg] at hr; unfold Reads at hr; omega
  refine ⟨ha, ?_⟩
  by_contra hb
  obtain ⟨g, hg, hr⟩ := hI 1 gs[0].b (by omega) (by omega) (by omega) 0 h (Or.inr rfl)
  rw [first g hg] at hr; unfold Reads at hr; omega

open Mod3SemBounds in
/-- `MOD3^1_6` is symmetric (`decide`, all pairs and all 64 rows). -/
theorem mod3_sym : SymOn 6 (· < 6) (mod3 1) := by
  have key : ∀ u < 6, ∀ v < 6, ∀ z ∈ allRows 6, mod3 1 (swapIn u v z) = mod3 1 z := by
    decide +kernel
  intro u v hu hv x hx
  exact key u hu v hv x (mem_allRows x 6 hx)

open Mod3SemBounds in
/-- `w2_5^1 = [2 x0 + x1 + … + x4 ≡ 1 mod 3]` is symmetric in `x1 … x4` (`symvars = (1, 2, 3, 4)`). -/
theorem w2_sym : SymOn 5 (fun i => 1 ≤ i ∧ i < 5) w2 := by
  have key : ∀ u < 5, ∀ v < 5, 1 ≤ u → 1 ≤ v → ∀ z ∈ allRows 5, w2 (swapIn u v z) = w2 z := by
    decide +kernel
  intro u v hu hv x hx
  exact key u hu.2 v hv.2 hu.1 hv.1 x (mem_allRows x 5 hx)

/-- **The r = 12 run's symmetry breaks are sound.** Every shaped, normal circuit computing
`MOD3^1_6` has one of the same length that also satisfies `order`, `symin` (all `u < v`, so in
particular `encode`'s consecutive form), `first01`, and `cubes.py`'s table clause. -/
theorem mod3_6_canonical (gs : List Gate) (o : ℕ) (neg : Bool) (hsh : Shaped 6 gs)
    (hnorm : Normal gs) (ho1 : 6 ≤ o) (ho2 : o < 6 + gs.length)
    (hc : ComputesAt 6 (mod3 1) gs o neg) :
    ∃ gs' o', gs'.length = gs.length ∧ Shaped 6 gs' ∧ Normal gs' ∧ 6 ≤ o' ∧
      o' < 6 + gs'.length ∧ ComputesAt 6 (mod3 1) gs' o' neg ∧ Order 6 gs' ∧
      SymInOrd (· < 6) gs' ∧ (∀ h : 0 < gs'.length, gs'[0].a = 0 ∧ gs'[0].b = 1 ∧ ¬ T100 gs'[0]) := by
  obtain ⟨gs', o', e, hs, hn, h1, h2, hc', hO, hI, hT⟩ :=
    canonical 6 (· < 6) (fun _ h => h) (mod3 1) mod3_sym neg gs o hsh hnorm ho1 ho2 hc
  refine ⟨gs', o', e, hs, hn, h1, h2, hc', hO, hI, fun h => ?_⟩
  obtain ⟨ha, hb⟩ := first01_of_symin 6 gs' hs hI h
  exact ⟨ha, hb, hT h (show gs'[0].a < 6 by omega) (show gs'[0].b < 6 by omega)⟩

/-- The same for `w2_5^1` with `symvars = (1, 2, 3, 4)`: `order`, `symin` on `x1 … x4`, and the
table clause for a first gate reading two of them (the encoding behind `size(w2_5^1) ≥ 10`). -/
theorem w2_canonical (gs : List Gate) (o : ℕ) (neg : Bool) (hsh : Shaped 5 gs)
    (hnorm : Normal gs) (ho1 : 5 ≤ o) (ho2 : o < 5 + gs.length)
    (hc : ComputesAt 5 Mod3SemBounds.w2 gs o neg) :
    ∃ gs' o', gs'.length = gs.length ∧ Shaped 5 gs' ∧ Normal gs' ∧ 5 ≤ o' ∧
      o' < 5 + gs'.length ∧ ComputesAt 5 Mod3SemBounds.w2 gs' o' neg ∧ Order 5 gs' ∧
      SymInOrd (fun i => 1 ≤ i ∧ i < 5) gs' ∧ TableOK (fun i => 1 ≤ i ∧ i < 5) gs' :=
  canonical 5 _ (fun _ h => h.2) _ w2_sym neg gs o hsh hnorm ho1 ho2 hc

/-! ### Checks on the definitions -/

open GateElim in
lemma order_of_check (n : ℕ) (gs : List Gate)
    (h : ∀ i < gs.length, i + 1 < gs.length → ¬ Reads (gs.getD (i + 1) dflt) (n + i) →
      ¬ PairLt (gs.getD (i + 1) dflt) (gs.getD i dflt)) : Order n gs := by
  intro i hi
  have := h i (by omega) hi
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at this

open GateElim in
lemma symin_of_check (n : ℕ) (gs : List Gate)
    (h : ∀ u < n, ∀ v < n, u < v → ∀ i < gs.length, Reads (gs.getD i dflt) v →
      ∃ g ∈ gs.take (i + 1), Reads g u) : SymInOrd (· < n) gs := by
  intro u v hu hv huv i hi hr
  exact h u hu v hv huv i hi (by rwa [List.getD_eq_getElem _ _ hi])

set_option synthInstance.maxSize 1024 in
open Mod3Upper Mod3SemBounds GateElim in
/-- The 13-gate circuit decoded from the r = 13 SAT model, which satisfies the CNF's clauses,
also satisfies these definitions. -/
theorem c13_satisfies : Shaped 6 c13 ∧ Normal c13 ∧ Order 6 c13 ∧ SymInOrd (· < 6) c13 ∧
    (∀ h : 0 < c13.length, c13[0].a = 0 ∧ c13[0].b = 1 ∧ ¬ T100 c13[0]) ∧
    ComputesAt 6 (mod3 1) c13 18 false := by
  refine ⟨(shaped_iff 6 c13).mpr (by decide), by decide, order_of_check 6 c13 (by decide),
    symin_of_check 6 c13 (by decide), fun _ => ⟨rfl, rfl, ?_⟩, ?_⟩
  · show ¬ T100 (g 0 1 false true true false); decide
  have key : ∀ z ∈ allRows 6, outAt z c13 18 false = mod3 1 z := by decide +kernel
  exact fun x hx => key x (mem_allRows x 6 hx)

/-! ### Controls -/

/-- `¬x0 ∧ x1`, which is not symmetric. -/
def notAnd (x : List Bool) : Bool := !x.getD 0 false && x.getD 1 false

def g100 : Gate := ⟨0, 1, fun p q => !p && q⟩

/-- Control: drop the symmetry hypothesis and the conclusion fails, even without `Order` and
`SymInOrd`. The only 1-gate circuits for `¬x0 ∧ x1` have table `(1, 0, 0)`. -/
theorem canonical_needs_symmetry :
    ¬ ∀ (n : ℕ) (S : ℕ → Prop) (_ : ∀ u, S u → u < n) (f : List Bool → Bool) (neg : Bool)
      (gs : List Gate) (o : ℕ), Shaped n gs → Normal gs → n ≤ o → o < n + gs.length →
      ComputesAt n f gs o neg →
      ∃ gs' o', gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧ n ≤ o' ∧
        o' < n + gs'.length ∧ ComputesAt n f gs' o' neg ∧ TableOK S gs' := by
  intro H
  have hc0 : ComputesAt 2 notAnd [g100] 2 false := by
    intro x hx
    match x, hx with
    | [p, q], _ => cases p <;> cases q <;> rfl
  obtain ⟨gs', o', hl, hs, hn, h1, h2, hc, hT⟩ := H 2 (· < 2) (fun _ h => h) notAnd false [g100] 2
    (by simp [Shaped, ShapedFrom, g100]) (by simp [Normal, g100]) le_rfl (by simp) hc0
  obtain ⟨g, rfl⟩ := List.length_eq_one_iff.mp hl
  simp only [Shaped, ShapedFrom] at hs
  have ho : o' = 2 := by simp at h2; omega
  have ha : g.a = 0 := by omega
  have hb : g.b = 1 := by omega
  subst ho
  have e : ∀ p q : Bool, g.op p q = (!p && q) := by
    intro p q
    have := hc [p, q] rfl
    simpa [outAt, run, step, ha, hb, notAnd] using this
  exact hT (by simp) (show g.a < 2 by omega) (show g.b < 2 by omega)
    (show T100 g from ⟨by rw [e]; rfl, by rw [e]; rfl, by rw [e]; rfl⟩)

/-- Control: each definition rejects a circuit that violates it. -/
theorem order_detects : ¬ Order 3 [⟨0, 2, fun p q => p && q⟩, ⟨0, 1, fun p q => p && q⟩] :=
  fun h => h 0 (by simp) (by decide) (by decide)

theorem symin_detects : ¬ SymInOrd (· < 3) [⟨1, 2, fun p q => p && q⟩] := by
  intro h
  obtain ⟨g, hg, hr⟩ := h 0 1 (by decide) (by decide) (by decide) 0 (by simp) (by decide)
  simp at hg; subst hg; revert hr; decide

theorem table_detects : ¬ TableOK (· < 2) [g100] :=
  fun h => h (by simp) (by decide) (by decide) ⟨rfl, rfl, rfl⟩

end SymCanon
