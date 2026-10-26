/-
# Semantic gate elimination, proved: the soundness of `sem`, `semxor`, `semeq` (and `elim`, `elim2`)

`research/circuits/optimal_circuit.encode` adds clauses `redundancy(T, B)`: on the row set `T`, at
most `B = r − size(h)` gates are *redundant*. A gate is redundant on `T` if there it computes a
constant, an input literal `±x_u`, or `±` an earlier gate. `h` is what the target becomes on `T`.
Until now the soundness of those clauses was argued in prose (the comment at the redundancy block,
and `research/circuits/RESULT.md`). This file proves it in `CircuitDual`'s bare B2 model (a gate
list, arbitrary 2-input tables, out-of-range reads give `false`, output = last node).

Proved (axioms: the standard three):
* `sem_elim`: for any circuit `gs` on `n` inputs and any row set `T`, on `T` the output is a
  constant, or an input literal, or it is computed by a nonempty circuit of at most
  `gs.length − redCount n gs T` gates. The construction (`build`) drops every redundant gate and
  rewires its readers to a representative, folding constants and negations into tables.
* `subst_out`: substituting each input by a constant or `±` a new input (`σ`) keeps the gate count.
* `sem_bound`: if `gs` computes `f`, `T` is the image of a substitution `σ` from `m` inputs, `f ∘ σ`
  is neither constant nor a literal, and every `m`-input circuit for `f ∘ σ` has `≥ s` gates, then
  `redCount n gs T + s ≤ gs.length`. This is the inequality each `redundancy(T, B)` clause asserts.
* `minimum_no_redundant`: in a minimum circuit no gate is redundant on all rows (`distinct`, and
  `sym`'s no-degenerate-gate half).
* `xor3_tight`: a worked instance (`XOR3`, `x2 := 0`) where the hypotheses hold and the bound is
  attained, so the statement with `+ 1` is false. Control: claiming `redCount = 0` there fails.

Not proved here:
* that the CNF's clauses say exactly this (the redundancy literals `d[g]` are forced true by the
  listed cases, and at most `B` are true: read by eye against `Redundant`);
* that each `T` the CNF uses is the image of a `σ` with `f ∘ σ` the function claimed (a subcube
  for `sem`, `x_u := ¬x_v` for `semxor`, `x_u := x_v` for `semeq`): a finite check per case;
* the lower bounds `s` themselves (`CERTIFIED`, `W2_LOWER`): SAT results, not Lean;
* that `elim`/`elim2`'s syntactic counts only count redundant gates (argued in `encode`'s docstring);
* the symmetry breaks (`order`, `first01`, `symin`, the table clause): proved in `SymCanon.lean`;
* `sym`'s no-dead-gate half, `allin`.
-/
import Garden.CircuitDual

namespace GateElim
open CircuitDual

/-! ### Run lemmas -/

lemma run_append (x : List Bool) (gs : List Gate) (g : Gate) :
    run x (gs ++ [g]) = step (run x gs) g := by
  simp [run, List.foldl_append]

lemma run_prefix (l : List Bool) (gs : List Gate) : ∃ t, run l gs = l ++ t := by
  induction gs generalizing l with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step l g)
    exact ⟨[g.op (l.getD g.a false) (l.getD g.b false)] ++ t, by simp [run] at ht ⊢; rw [ht]; simp [step]⟩

lemma run_split (x : List Bool) (gs : List Gate) (j : ℕ) :
    run x gs = run (run x (gs.take j)) (gs.drop j) := by
  have h : run x (gs.take j ++ gs.drop j) = run (run x (gs.take j)) (gs.drop j) := by
    simp only [run, List.foldl_append]
  rw [List.take_append_drop] at h; exact h

lemma run_take_getD (x : List Bool) (gs : List Gate) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run x gs).getD i false = (run x (gs.take j)).getD i false := by
  rw [run_split x gs j]
  obtain ⟨t, ht⟩ := run_prefix (run x (gs.take j)) (gs.drop j)
  rw [ht, List.getD_append]
  rw [run_length, List.length_take, min_eq_left hj]; exact hi

lemma take_succ' (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gs.take (j + 1) = gs.take j ++ [gs[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl

lemma getD_out (x : List Bool) (gs : List Gate) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run x gs).getD i false = false := by
  rw [List.getD_eq_default]; rw [run_length]; exact hi

lemma gate_val (x : List Bool) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (run x (gs.take (j + 1))).getD (x.length + j) false =
      gs[j].op ((run x (gs.take j)).getD gs[j].a false) ((run x (gs.take j)).getD gs[j].b false) := by
  rw [take_succ' gs j hj, run_append, step, getD_append_single, run_length,
    List.length_take, min_eq_left hj.le]
  simp

lemma take_succ_getD_ne (x : List Bool) (gs : List Gate) (j i : ℕ) (hj : j < gs.length)
    (hi : i ≠ x.length + j) :
    (run x (gs.take (j + 1))).getD i false = (run x (gs.take j)).getD i false := by
  rw [take_succ' gs j hj, run_append, step, getD_append_single, run_length,
    List.length_take, min_eq_left hj.le]
  split_ifs with h1
  · rfl
  · rw [getD_out]; rw [List.length_take, min_eq_left hj.le]; omega

/-! ### Redundancy, and the deletion construction -/

/-- Node `i`'s value on input `x`. -/
def V (gs : List Gate) (x : List Bool) (i : ℕ) : Bool := (run x gs).getD i false

/-- Gate `j` (node `n + j`) is redundant on the rows `T`: there it computes a constant, an input
literal `±x_u`, or `±` an earlier gate. This is the definition `optimal_circuit.encode`'s
`redundancy` clauses use. -/
def Redundant (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (j : ℕ) : Prop :=
  (∃ c : Bool, ∀ x ∈ T, V gs x (n + j) = c) ∨
  (∃ u < n, ∃ b : Bool, ∀ x ∈ T, V gs x (n + j) = (b ^^ x.getD u false)) ∨
  (∃ h < j, ∃ b : Bool, ∀ x ∈ T, V gs x (n + j) = (b ^^ V gs x (n + h)))

/-- Where an old node now lives: a constant, or a node of the new circuit, possibly negated. -/
inductive Rep
  | const (c : Bool)
  | lit (k : ℕ) (b : Bool)

namespace Rep
def eval (vals : List Bool) : Rep → Bool
  | const c => c
  | lit k b => b ^^ vals.getD k false
def neg (b : Bool) : Rep → Rep
  | const c => const (b ^^ c)
  | lit k b' => lit k (b ^^ b')
def node : Rep → ℕ
  | const _ => 0
  | lit k _ => k
def fix : Rep → Bool → Bool
  | const c, _ => c
  | lit _ b, u => b ^^ u
def Lt (m : ℕ) : Rep → Prop
  | const _ => True
  | lit k _ => k < m

lemma eval_neg (vals : List Bool) (b : Bool) (r : Rep) : (r.neg b).eval vals = (b ^^ r.eval vals) := by
  cases r <;> simp [neg, eval]

lemma fix_node (vals : List Bool) (r : Rep) : r.fix (vals.getD r.node false) = r.eval vals := by
  cases r <;> rfl

lemma Lt_neg (m : ℕ) (b : Bool) (r : Rep) (h : r.Lt m) : (r.neg b).Lt m := by
  cases r <;> simp_all [neg, Lt]

lemma Lt_mono {m m' : ℕ} (hm : m ≤ m') (r : Rep) (h : r.Lt m) : r.Lt m' := by
  cases r <;> simp_all [Lt]; omega

lemma eval_append (vals t : List Bool) (r : Rep) (h : r.Lt vals.length) :
    r.eval (vals ++ t) = r.eval vals := by
  cases r with
  | const c => rfl
  | lit k b => simp only [eval]; rw [List.getD_append _ _ _ _ h]
end Rep

/-- The new gate replacing an old one: read where its arguments now live, and fold constants and
negations into the table. -/
def newGate (g : Gate) (ρ : ℕ → Rep) : Gate :=
  { a := (ρ g.a).node, b := (ρ g.b).node, op := fun u v => g.op ((ρ g.a).fix u) ((ρ g.b).fix v) }

def dflt : Gate := ⟨0, 0, fun _ _ => false⟩

open Classical in
/-- The representative chosen for a redundant gate `j`, given the map `ρ` for earlier nodes. -/
noncomputable def repOf (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (j : ℕ) (ρ : ℕ → Rep) : Rep :=
  if h1 : ∃ c : Bool, ∀ x ∈ T, V gs x (n + j) = c then .const h1.choose
  else if h2 : ∃ p : ℕ × Bool, p.1 < n ∧ ∀ x ∈ T, V gs x (n + j) = (p.2 ^^ x.getD p.1 false) then
    .lit h2.choose.1 h2.choose.2
  else if h3 : ∃ p : ℕ × Bool, p.1 < j ∧ ∀ x ∈ T, V gs x (n + j) = (p.2 ^^ V gs x (n + p.1)) then
    (ρ (n + h3.choose.1)).neg h3.choose.2
  else .const false

open Classical in
/-- Process the first `j` gates: drop the redundant ones, rewire the rest. -/
noncomputable def build (n : ℕ) (gs : List Gate) (T : Set (List Bool)) : ℕ → List Gate × (ℕ → Rep)
  | 0 => ([], fun i => if i < n then .lit i false else .const false)
  | j + 1 =>
    let s := build n gs T j
    if Redundant n gs T j then (s.1, Function.update s.2 (n + j) (repOf n gs T j s.2))
    else (s.1 ++ [newGate (gs.getD j dflt) s.2],
          Function.update s.2 (n + j) (.lit (n + s.1.length) false))

lemma run_getD_input (x : List Bool) (gs : List Gate) (k : ℕ) (hk : k < x.length) :
    (run x gs).getD k false = x.getD k false := by
  obtain ⟨t, ht⟩ := run_prefix x gs
  rw [ht, List.getD_append _ _ _ _ hk]

lemma redundant_cases {n : ℕ} {gs : List Gate} {T : Set (List Bool)} {j : ℕ}
    (h : Redundant n gs T j) :
    (∃ c : Bool, ∀ x ∈ T, V gs x (n + j) = c) ∨
    (∃ p : ℕ × Bool, p.1 < n ∧ ∀ x ∈ T, V gs x (n + j) = (p.2 ^^ x.getD p.1 false)) ∨
    (∃ p : ℕ × Bool, p.1 < j ∧ ∀ x ∈ T, V gs x (n + j) = (p.2 ^^ V gs x (n + p.1))) := by
  rcases h with h | ⟨u, hu, b, hb⟩ | ⟨k, hk, b, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨(u, b), hu, hb⟩)
  · exact Or.inr (Or.inr ⟨(k, b), hk, hb⟩)

theorem build_inv (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (hT : ∀ x ∈ T, x.length = n) :
    ∀ j ≤ gs.length,
      (∀ i, ((build n gs T j).2 i).Lt (n + (build n gs T j).1.length)) ∧
      (∀ x ∈ T, ∀ i, (run x (gs.take j)).getD i false =
        ((build n gs T j).2 i).eval (run x (build n gs T j).1)) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun i => ?_, fun x hx i => ?_⟩
    · simp only [build]; split_ifs with h <;> simp [Rep.Lt]; omega
    · simp only [build, List.take_zero]
      split_ifs with h
      · simp [Rep.eval, run]
      · simp only [Rep.eval, run, List.foldl_nil]
        rw [List.getD_eq_default]; rw [hT x hx]; omega
  | succ j ih =>
    intro hj
    have hj' : j < gs.length := by omega
    obtain ⟨hLt, hEv⟩ := ih (by omega)
    set s := build n gs T j with hs
    have hV : ∀ x ∈ T, V gs x (n + j) = (run x (gs.take (j + 1))).getD (n + j) false := by
      intro x hx; unfold V; rw [run_take_getD x gs (j + 1) _ (by omega) (by rw [hT x hx]; omega)]
    have hold : ∀ x ∈ T, ∀ i, i ≠ n + j →
        (run x (gs.take (j + 1))).getD i false = (run x (gs.take j)).getD i false := by
      intro x hx i hi; exact take_succ_getD_ne x gs j i hj' (by rw [hT x hx]; exact hi)
    by_cases hred : Redundant n gs T j
    · have hb : build n gs T (j + 1) = (s.1, Function.update s.2 (n + j) (repOf n gs T j s.2)) := by
        simp only [build, if_pos hred, hs]
      rw [hb]; dsimp only
      refine ⟨fun i => ?_, fun x hx i => ?_⟩
      · by_cases hi : i = n + j
        · subst hi; simp only [Function.update_self]
          unfold repOf; split_ifs with h1 h2 h3
          · trivial
          · simp only [Rep.Lt]; have := h2.choose_spec.1; omega
          · exact Rep.Lt_neg _ _ _ (hLt _)
          · trivial
        · rw [Function.update_of_ne hi]; exact hLt i
      · by_cases hi : i = n + j
        · subst hi; simp only [Function.update_self]
          rw [← hV x hx]
          unfold repOf; split_ifs with h1 h2 h3
          · exact h1.choose_spec x hx
          · simp only [Rep.eval]
            rw [run_getD_input _ _ _ (by rw [hT x hx]; exact h2.choose_spec.1)]
            exact h2.choose_spec.2 x hx
          · rw [Rep.eval_neg, ← hEv x hx, h3.choose_spec.2 x hx]
            unfold V
            rw [run_take_getD x gs j _ hj'.le
              (by rw [hT x hx]; exact Nat.add_lt_add_left h3.choose_spec.1 n)]
          · exfalso
            rcases redundant_cases hred with h | h | h
            · exact h1 h
            · exact h2 h
            · exact h3 h
        · rw [Function.update_of_ne hi, hold x hx i hi]; exact hEv x hx i
    · have hb : build n gs T (j + 1) = (s.1 ++ [newGate (gs.getD j dflt) s.2],
          Function.update s.2 (n + j) (.lit (n + s.1.length) false)) := by
        simp only [build, if_neg hred, hs]
      rw [hb]; dsimp only
      have hlen : ∀ x ∈ T, (run x s.1).length = n + s.1.length := by
        intro x hx; rw [run_length, hT x hx]
      refine ⟨fun i => ?_, fun x hx i => ?_⟩
      · by_cases hi : i = n + j
        · subst hi; simp [Rep.Lt]
        · rw [Function.update_of_ne hi]
          exact Rep.Lt_mono (by simp) _ (hLt i)
      · rw [run_append, step]
        by_cases hi : i = n + j
        · subst hi; simp only [Function.update_self, Rep.eval]
          rw [getD_append_single, if_neg (by rw [hlen x hx]; omega), if_pos (hlen x hx).symm]
          rw [← hV x hx]; unfold V
          rw [run_take_getD x gs (j + 1) _ (by omega) (by rw [hT x hx]; omega)]
          have := gate_val x gs j hj'
          rw [hT x hx] at this
          rw [this, hEv x hx, hEv x hx]
          simp only [newGate, Rep.fix_node, List.getD_eq_getElem _ _ hj', Bool.false_xor]
        · rw [Function.update_of_ne hi, hold x hx i hi, hEv x hx i]
          exact (Rep.eval_append _ _ _ (by rw [hlen x hx]; exact hLt i)).symm

open Classical in
/-- The number of gates of `gs` that are redundant on `T`. -/
noncomputable def redCount (n : ℕ) (gs : List Gate) (T : Set (List Bool)) : ℕ :=
  ((Finset.range gs.length).filter (fun j => Redundant n gs T j)).card

open Classical in
lemma build_count (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (j : ℕ) :
    (build n gs T j).1.length + ((Finset.range j).filter (fun h => Redundant n gs T h)).card = j := by
  induction j with
  | zero => simp [build]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hred : Redundant n gs T j
    · rw [if_pos hred, Finset.card_insert_of_notMem (by simp)]
      simp only [build, if_pos hred]; omega
    · simp only [build, if_neg hred, List.length_append, List.length_singleton]; omega

def negOut (b : Bool) (g : Gate) : Gate := ⟨g.a, g.b, fun u v => b ^^ g.op u v⟩

lemma out_snoc (x : List Bool) (L : List Gate) (g : Gate) :
    out x (L ++ [g]) = g.op ((run x L).getD g.a false) ((run x L).getD g.b false) := by
  simp [out, run_append, step]

/-- **Semantic gate elimination.** Let `gs` be a circuit on `n` inputs (output: its last node) and
`T` a set of rows. Then on `T` the output is a constant, or an input literal, or it is computed by
a nonempty circuit with at most `gs.length − redCount n gs T` gates. -/
theorem sem_elim (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (hT : ∀ x ∈ T, x.length = n)
    (hne : gs ≠ []) :
    (∃ c : Bool, ∀ x ∈ T, out x gs = c) ∨
    (∃ u < n, ∃ b : Bool, ∀ x ∈ T, out x gs = (b ^^ x.getD u false)) ∨
    (∃ gs' : List Gate, gs' ≠ [] ∧ gs'.length + redCount n gs T ≤ gs.length ∧
      ∀ x ∈ T, out x gs' = out x gs) := by
  have hr : gs.length ≠ 0 := by simpa using hne
  obtain ⟨hLt, hEv⟩ := build_inv n gs T hT gs.length le_rfl
  have hcnt := build_count n gs T gs.length
  set acc := (build n gs T gs.length).1
  set ρ := (build n gs T gs.length).2
  have hout : ∀ x ∈ T, out x gs = (ρ (n + gs.length - 1)).eval (run x acc) := by
    intro x hx
    have := hEv x hx (n + gs.length - 1)
    rw [List.take_length] at this
    rw [← this, out, getLastD_eq_getD, run_length, hT x hx]
  have hL := hLt (n + gs.length - 1)
  generalize hR : ρ (n + gs.length - 1) = R at hout hL
  cases R with
  | const c => exact Or.inl ⟨c, fun x hx => by rw [hout x hx]; rfl⟩
  | lit k b =>
    by_cases hk : k < n
    · refine Or.inr (Or.inl ⟨k, hk, b, fun x hx => ?_⟩)
      rw [hout x hx, Rep.eval, run_getD_input _ _ _ (by rw [hT x hx]; exact hk)]
    · simp only [Rep.Lt] at hL
      obtain ⟨m, rfl⟩ : ∃ m, k = n + m := ⟨k - n, by omega⟩
      have hm : m < acc.length := by omega
      refine Or.inr (Or.inr ⟨acc.take m ++ [negOut b acc[m]], by simp, ?_, fun x hx => ?_⟩)
      · simp only [List.length_append, List.length_take, List.length_singleton, redCount]; omega
      · rw [hout x hx, out_snoc, Rep.eval]
        rw [run_take_getD x acc (m + 1) _ hm (by rw [hT x hx]; omega)]
        have := gate_val x acc m hm
        rw [hT x hx] at this
        rw [this]; rfl

theorem redCount_le (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (hT : ∀ x ∈ T, x.length = n)
    (f : List Bool → Bool) (s : ℕ) (hne : gs ≠ []) (hgs : ∀ x ∈ T, out x gs = f x)
    (hc : ¬ ∃ c : Bool, ∀ x ∈ T, f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x ∈ T, f x = (b ^^ x.getD u false))
    (hlb : ∀ gs' : List Gate, gs' ≠ [] → (∀ x ∈ T, out x gs' = f x) → s ≤ gs'.length) :
    redCount n gs T + s ≤ gs.length := by
  rcases sem_elim n gs T hT hne with ⟨c, h⟩ | ⟨u, hu, b, h⟩ | ⟨gs', hne', hlen, h⟩
  · exact absurd ⟨c, fun x hx => (hgs x hx) ▸ h x hx⟩ hc
  · exact absurd ⟨u, hu, b, fun x hx => (hgs x hx) ▸ h x hx⟩ hl
  · have := hlb gs' hne' (fun x hx => (h x hx).trans (hgs x hx)); omega

/-- **`distinct`, and `sym`'s no-degenerate-gate half.** In a minimum circuit for a function that
is neither constant nor a literal, no gate is redundant on the full row set: none computes a
constant, `±x_u`, or `±` an earlier gate. (A degenerate gate computes `0` or one of its own
inputs, so it is redundant.) -/
theorem minimum_no_redundant (n : ℕ) (gs : List Gate) (f : List Bool → Bool) (hne : gs ≠ [])
    (hgs : ∀ x : List Bool, x.length = n → out x gs = f x)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (hmin : ∀ gs' : List Gate, gs' ≠ [] → (∀ x : List Bool, x.length = n → out x gs' = f x) →
      gs.length ≤ gs'.length) :
    redCount n gs {x | x.length = n} = 0 := by
  have := redCount_le n gs {x | x.length = n} (fun x hx => hx) f gs.length hne
    (fun x hx => hgs x hx) (fun ⟨c, h⟩ => hc ⟨c, fun x hx => h x hx⟩)
    (fun ⟨u, hu, b, h⟩ => hl ⟨u, hu, b, fun x hx => h x hx⟩)
    (fun gs' h1 h2 => hmin gs' h1 (fun x hx => h2 x hx))
  omega

/-! ### Substituting the inputs

`σ i` says what old input `i < n` becomes over `m` new inputs: a constant, or `±y_k`. Every gate
keeps its table up to folding, so the gate count is unchanged. -/

/-- Where an old node goes under the substitution: inputs by `σ`, gate nodes shifted. -/
def mv (n m : ℕ) (σ : ℕ → Rep) (i : ℕ) : Rep := if i < n then σ i else .lit (i - n + m) false

def substGate (n m : ℕ) (σ : ℕ → Rep) (g : Gate) : Gate :=
  ⟨(mv n m σ g.a).node, (mv n m σ g.b).node,
    fun u v => g.op ((mv n m σ g.a).fix u) ((mv n m σ g.b).fix v)⟩

/-- The old input row produced by the new row `y`. -/
def inRow (n : ℕ) (σ : ℕ → Rep) (y : List Bool) : List Bool := (List.range n).map fun i => (σ i).eval y

def SRel (n m : ℕ) (σ : ℕ → Rep) (lx ly : List Bool) : Prop :=
  n ≤ lx.length ∧ m ≤ ly.length ∧ lx.length + m = ly.length + n ∧
    (∀ i < n, (σ i).Lt m) ∧ ∀ i, lx.getD i false = (mv n m σ i).eval ly

lemma srel_step (n m : ℕ) (σ : ℕ → Rep) (lx ly : List Bool) (g : Gate) (h : SRel n m σ lx ly) :
    SRel n m σ (step lx g) (step ly (substGate n m σ g)) := by
  obtain ⟨hn, hm, hl, hσ, hv⟩ := h
  have lt : ∀ i, i < lx.length → (mv n m σ i).Lt ly.length := by
    intro i hi; unfold mv; split_ifs with h
    · exact Rep.Lt_mono hm _ (hσ i h)
    · simp [Rep.Lt]; omega
  refine ⟨by simp [step]; omega, by simp [step]; omega, by simp [step]; omega, hσ, fun i => ?_⟩
  simp only [step]
  rw [getD_append_single]
  split_ifs with h1 h2
  · rw [Rep.eval_append _ _ _ (lt i h1), hv i]
  · subst h2
    have : mv n m σ lx.length = .lit ly.length false := by
      unfold mv; rw [if_neg (by omega)]; congr 1; omega
    rw [this, Rep.eval, getD_append_single, if_neg (lt_irrefl _), if_pos rfl]
    simp only [substGate, Rep.fix_node, Bool.false_xor, ← hv]
  · have : mv n m σ i = .lit (i - n + m) false := by unfold mv; rw [if_neg (by omega)]
    rw [this, Rep.eval, List.getD_eq_default _ _ (by simp; omega)]; rfl

lemma srel_run (n m : ℕ) (σ : ℕ → Rep) (gs : List Gate) : ∀ lx ly, SRel n m σ lx ly →
    SRel n m σ (run lx gs) (run ly (gs.map (substGate n m σ))) := by
  induction gs with
  | nil => intro lx ly h; simpa [run] using h
  | cons g gs ih => intro lx ly h; simpa [run] using ih _ _ (srel_step n m σ lx ly g h)

/-- Substituting inputs costs no gates: the substituted circuit, on any new row `y` of length `m`,
outputs what the old circuit outputs on the old row `inRow n σ y`. -/
theorem subst_out (n m : ℕ) (σ : ℕ → Rep) (hσ : ∀ i < n, (σ i).Lt m) (gs : List Gate)
    (hne : gs ≠ []) (y : List Bool) (hy : y.length = m) :
    out y (gs.map (substGate n m σ)) = out (inRow n σ y) gs := by
  have h0 : SRel n m σ (inRow n σ y) y := by
    refine ⟨by simp [inRow], by omega, by simp [inRow]; omega, hσ, fun i => ?_⟩
    unfold mv inRow
    split_ifs with h
    · simp [List.getD_eq_getElem?_getD, h]
    · rw [List.getD_eq_default _ _ (by simp; omega), Rep.eval, List.getD_eq_default _ _ (by omega)]
      rfl
  have h := srel_run n m σ gs _ _ h0
  have hr : gs.length ≠ 0 := by simpa using hne
  have hlx : (inRow n σ y).length = n := by simp [inRow]
  unfold out
  rw [getLastD_eq_getD, getLastD_eq_getD, h.2.2.2.2, run_length, run_length, hlx]
  have : mv n m σ (n + gs.length - 1) = .lit (y.length + (gs.map (substGate n m σ)).length - 1) false := by
    unfold mv; rw [if_neg (by omega)]; simp; omega
  rw [this, Rep.eval]; simp

/-- **The bound behind `encode`'s `redundancy(T, B)` clauses.** Let `gs` compute `f` on all rows
of length `n`, and let the rows `T` be the image of an input substitution `σ` from `m` new inputs.
Let `g = f ∘ σ`, which is neither constant nor a literal, and suppose every `m`-input circuit for
`g` has at least `s` gates. Then at most `gs.length − s` gates of `gs` are redundant on `T`.
`sem` is the case where `σ` fixes the inputs in `S` and renames the rest; `semxor` and `semeq` are
`x_u := ¬x_v` and `x_u := x_v`. -/
theorem sem_bound (n m : ℕ) (σ : ℕ → Rep) (hσ : ∀ i < n, (σ i).Lt m)
    (f : List Bool → Bool) (gs : List Gate) (hne : gs ≠ [])
    (hgs : ∀ x : List Bool, x.length = n → out x gs = f x) (s : ℕ)
    (hc : ¬ ∃ c : Bool, ∀ y : List Bool, y.length = m → f (inRow n σ y) = c)
    (hl : ¬ ∃ k < m, ∃ b : Bool, ∀ y : List Bool, y.length = m → f (inRow n σ y) = (b ^^ y.getD k false))
    (hlb : ∀ gs' : List Gate, gs' ≠ [] →
      (∀ y : List Bool, y.length = m → out y gs' = f (inRow n σ y)) → s ≤ gs'.length) :
    redCount n gs {x | ∃ y : List Bool, y.length = m ∧ x = inRow n σ y} + s ≤ gs.length := by
  have hlen : ∀ y : List Bool, (inRow n σ y).length = n := by intro y; simp [inRow]
  apply redCount_le n gs _ (by rintro x ⟨y, -, rfl⟩; exact hlen y) f s hne
    (by rintro x ⟨y, -, rfl⟩; exact hgs _ (hlen y))
  · rintro ⟨c, h⟩; exact hc ⟨c, fun y hy => h _ ⟨y, hy, rfl⟩⟩
  · rintro ⟨u, hu, b, h⟩
    have hrow : ∀ y : List Bool, (inRow n σ y).getD u false = (σ u).eval y := by
      intro y; simp [inRow, List.getD_eq_getElem?_getD, hu]
    have hσu := hσ u hu
    generalize hR : σ u = R at hrow hσu
    cases R with
    | const c => exact hc ⟨b ^^ c, fun y hy => by rw [h _ ⟨y, hy, rfl⟩, hrow]; rfl⟩
    | lit k b' =>
      exact hl ⟨k, hσu, b ^^ b', fun y hy => by
        rw [h _ ⟨y, hy, rfl⟩, hrow, Rep.eval, Bool.xor_assoc]⟩
  · intro gs' hne' hagree
    have := hlb (gs'.map (substGate n m σ)) (by simpa using hne') (fun y hy => by
      rw [subst_out n m σ hσ gs' hne' y hy]; exact hagree _ ⟨y, hy, rfl⟩)
    simpa using this

/-! ### A worked instance, which also serves as the control

`XOR3` by two gates, restricted by `x2 := 0` to `XOR2` (size ≥ 1, trivially). `sem_bound` gives
`redCount ≤ 1`, and the output gate *is* redundant there (it equals gate 0), so `redCount = 1`:
the hypotheses are satisfiable and the bound is attained, so `sem_bound` with `+ 1` added to its
left side is false. -/

def xorG (a b : ℕ) : Gate := ⟨a, b, fun u v => u ^^ v⟩
def xor3c : List Gate := [xorG 0 1, xorG 3 2]
def σ0 : ℕ → Rep := fun i => if i = 0 then .lit 0 false else if i = 1 then .lit 1 false else .const false
def T0 : Set (List Bool) := {x | ∃ y : List Bool, y.length = 2 ∧ x = inRow 3 σ0 y}
def xor3 (x : List Bool) : Bool := x.getD 0 false ^^ x.getD 1 false ^^ x.getD 2 false

lemma inRow_σ0 (a b : Bool) : inRow 3 σ0 [a, b] = [a, b, false] := by
  simp [inRow, σ0, List.range_succ, Rep.eval]

theorem xor3_bound : redCount 3 xor3c T0 + 1 ≤ 2 := by
  have h := sem_bound 3 2 σ0 (by intro i hi; interval_cases i <;> simp [σ0, Rep.Lt]) xor3 xor3c
    (by simp [xor3c]) (by
      intro x hx; obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hx
      simp [out, run, step, xor3c, xorG, xor3]) 1
    (by
      rintro ⟨c, h⟩
      have h1 := h [false, false] rfl; have h2 := h [true, false] rfl
      simp [inRow_σ0, xor3] at h1 h2; rw [h1] at h2; exact absurd h2 (by decide))
    (by
      rintro ⟨k, hk, b, h⟩
      have h1 := h [false, false] rfl; have h2 := h [true, false] rfl; have h3 := h [false, true] rfl
      simp [inRow_σ0, xor3] at h1 h2 h3
      interval_cases k <;> simp_all)
    (by intro gs' hne _; exact List.length_pos_iff.mpr hne)
  exact h

open Classical in
theorem xor3_redundant : 1 ≤ redCount 3 xor3c T0 := by
  unfold redCount
  apply Finset.card_pos.mpr
  refine ⟨1, Finset.mem_filter.mpr ⟨by simp [xor3c], ?_⟩⟩
  refine Or.inr (Or.inr ⟨0, by omega, false, ?_⟩)
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hy
  simp [V, inRow_σ0, run, step, xor3c, xorG]

theorem xor3_tight : redCount 3 xor3c T0 = 1 := by
  have := xor3_bound; have := xor3_redundant; omega

end GateElim
