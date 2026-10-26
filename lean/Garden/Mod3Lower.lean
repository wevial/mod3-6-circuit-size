/-
# size(MOD3^1_6) ≥ 13, from exactly what the SAT runs certify

`research/circuits/` refutes, for every r ≤ 12, a CNF that says "an r-gate circuit of the CNF's
shape computes MOD3^1_6 and satisfies these constraints". `Admissible gs o neg` below is that
sentence in Lean, one field per clause family of `optimal_circuit.encode` and `cubes.py`:

| field | clause family |
|---|---|
| `shaped`, `normal`, `out_lo`, `out_hi`, `computes` | the encoding itself (`sel`, `fbit` with `f00 = 0`, `val`, `outsel`, `neg`) |
| `nondegenerate`, `used` | `sym` (i) no table `0`, `x_j`, `x_k`; (ii) every gate is the output or read later |
| `order`, `symin`, `first01_table` | `order`; `symin`; `first01` and `cubes.py`'s table clause |
| `allin` | `allin` |
| `distinct` | `distinct` |
| `elim`, `elim2` | `elim`, `elim2` (`K` and `e` at their least values) |
| `sem1`, `sem2`, `semxor`, `semeq` | `sem` (k = 1, 2), `semxor`, `semeq` (`redundancy(T, B)`) |

Proved (axioms: the standard three):
* `mod3_6_lower`: if no `Admissible` circuit has ≤ 12 gates, then every circuit computing
  `MOD3^1_6` has ≥ 13 gates (`LB 6 (mod3 1) 13`). Hypotheses besides that one: the smaller sizes
  `sem` uses (`LB 5 (mod3 q) (c5 q)`, `LB 4 (mod3 q) (c4 q)`, `LB 5 w2 10`), as in
  `Mod3SemBounds`.
* `elim_redundant`, `elim2_redundant`: the gates `elim`/`elim2` count are redundant on their
  restriction, so their bounds follow from `sem`'s.

So the lower bound now rests on: (1) for each r ≤ 12, the CNF that `optimal_circuit.encode` (and
`cubes.py`, for r = 12) builds is satisfied by every `Admissible` circuit of r gates (read by eye,
field by field, against the table above); (2) that CNF is unsatisfiable (LRAT certificates checked
by Lean's verified checker, plus the cube cover); (3) the smaller sizes, each a SAT result of its
own. The r ≤ 11 runs used a subset of these clause families, which only makes (1) easier.

(3) is discharged in `Mod3Tower.lean` (2026-10-24 20:53): `mod3_6_lower_sat` proves the same
conclusion from the runs' SAT sides alone, and `full6_iff` shows its r = 12 hypothesis is
`Admissible` here.
-/
import Garden.Reduction
import Garden.Mod3SemBounds

namespace Mod3Lower
open CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds

/-! ### `elim` and `elim2` count only redundant gates -/

/-- `encode`'s `K[g, c]` for input `v`: gate `g` reads `x_v` in a slot that `x_v = c` makes its
table constant in. -/
def KC (v : ℕ) (c : Bool) (g : Gate) : Prop :=
  (g.a = v ∧ g.op c false = g.op c true) ∨ (g.b = v ∧ g.op false c = g.op true c)

/-- `elim`'s count for `x_v = c`: gate `j` reads `x_v`, or reads a gate in `KC v c`. -/
def ElimHit (n v : ℕ) (c : Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ h : j < gs.length, Reads gs[j] v ∨
    ∃ k, ∃ hk : k < j, Reads gs[j] (n + k) ∧ KC v c (gs[k]'(by omega))

/-- `elim2`'s count for `x_u = a, x_v = b`: gate `j` reads `x_u` or `x_v`, or reads a gate made
constant by `a`, by `b`, or by reading both. -/
def Elim2Hit (n u v : ℕ) (a b : Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ h : j < gs.length, Reads gs[j] u ∨ Reads gs[j] v ∨
    ∃ k, ∃ hk : k < j, Reads gs[j] (n + k) ∧
      (KC u a (gs[k]'(by omega)) ∨ KC v b (gs[k]'(by omega)) ∨
        ((gs[k]'(by omega)).a = u ∧ (gs[k]'(by omega)).b = v))

open Classical in
noncomputable def elimCount (n v : ℕ) (c : Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter (ElimHit n v c gs)).card

open Classical in
noncomputable def elim2Count (n u v : ℕ) (a b : Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter (Elim2Hit n u v a b gs)).card

/-- A node constant on `T`, read by gate `j`, makes gate `j` redundant on `T`. -/
lemma redundant_of_reads_const (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (T : Set (List Bool))
    (hT : ∀ x ∈ T, x.length = n) (j : ℕ) (hj : j < gs.length) (c : ℕ) (hr : Reads gs[j] c)
    (hconst : ∃ d, ∀ x ∈ T, V gs x c = d) : Redundant n gs T j := by
  have := (shaped_iff n gs).mp hs j hj
  apply redundant_of_const_arg n gs T hT j hj (by omega) (by omega)
  rcases hr with h | h
  · exact Or.inl (h ▸ hconst)
  · exact Or.inr (h ▸ hconst)

/-- An input is constant on rows that fix it. -/
lemma input_const (n : ℕ) (gs : List Gate) (T : Set (List Bool)) (hT : ∀ x ∈ T, x.length = n)
    (v : ℕ) (hv : v < n) (c : Bool) (hc : ∀ x ∈ T, x.getD v false = c) :
    ∃ d, ∀ x ∈ T, V gs x v = d :=
  ⟨c, fun x hx => by unfold V; rw [run_getD_input _ _ _ (by rw [hT x hx]; exact hv), hc x hx]⟩

/-- A gate in `KC v c` is constant on rows with `x_v = c`. -/
lemma kc_const (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (T : Set (List Bool))
    (hT : ∀ x ∈ T, x.length = n) (v : ℕ) (hv : v < n) (c : Bool)
    (hc : ∀ x ∈ T, x.getD v false = c) (k : ℕ) (hk : k < gs.length) (hK : KC v c gs[k]) :
    ∃ d, ∀ x ∈ T, V gs x (n + k) = d := by
  have hsk := (shaped_iff n gs).mp hs k hk
  have hval : ∀ x ∈ T, V gs x v = c := by
    intro x hx; unfold V; rw [run_getD_input _ _ _ (by rw [hT x hx]; exact hv), hc x hx]
  rcases hK with ⟨ha, hop⟩ | ⟨hb, hop⟩
  · refine ⟨gs[k].op c false, fun x hx => ?_⟩
    rw [V_gate n x (hT x hx) gs k hk (by omega) (by omega), ha, hval x hx]
    cases V gs x gs[k].b
    · rfl
    · exact hop.symm
  · refine ⟨gs[k].op false c, fun x hx => ?_⟩
    rw [V_gate n x (hT x hx) gs k hk (by omega) (by omega), hb, hval x hx]
    cases V gs x gs[k].a
    · rfl
    · exact hop.symm

/-- **Every gate `elim` counts at `x_v = c` is redundant there.** -/
theorem elim_redundant (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (v : ℕ) (hv : v < n)
    (c : Bool) (j : ℕ) (h : ElimHit n v c gs j) :
    Redundant n gs {x | x.length = n ∧ x.getD v false = c} j := by
  set T := {x : List Bool | x.length = n ∧ x.getD v false = c}
  have hT : ∀ x ∈ T, x.length = n := fun x hx => hx.1
  have hc : ∀ x ∈ T, x.getD v false = c := fun x hx => hx.2
  obtain ⟨hj, hr | ⟨k, hk, hr, hK⟩⟩ := h
  · exact redundant_of_reads_const n gs hs T hT j hj v hr (input_const n gs T hT v hv c hc)
  · exact redundant_of_reads_const n gs hs T hT j hj (n + k) hr
      (kc_const n gs hs T hT v hv c hc k (by omega) hK)

/-- **Every gate `elim2` counts at `x_u = a, x_v = b` is redundant there.** -/
theorem elim2_redundant (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (u v : ℕ) (hu : u < n)
    (hv : v < n) (a b : Bool) (j : ℕ) (h : Elim2Hit n u v a b gs j) :
    Redundant n gs {x | x.length = n ∧ (x.getD u false = a ∧ x.getD v false = b)} j := by
  set T := {x : List Bool | x.length = n ∧ (x.getD u false = a ∧ x.getD v false = b)}
  have hT : ∀ x ∈ T, x.length = n := fun x hx => hx.1
  have ha : ∀ x ∈ T, x.getD u false = a := fun x hx => hx.2.1
  have hb : ∀ x ∈ T, x.getD v false = b := fun x hx => hx.2.2
  obtain ⟨hj, hr | hr | ⟨k, hk, hr, hK | hK | ⟨hka, hkb⟩⟩⟩ := h
  · exact redundant_of_reads_const n gs hs T hT j hj u hr (input_const n gs T hT u hu a ha)
  · exact redundant_of_reads_const n gs hs T hT j hj v hr (input_const n gs T hT v hv b hb)
  · exact redundant_of_reads_const n gs hs T hT j hj (n + k) hr
      (kc_const n gs hs T hT u hu a ha k (by omega) hK)
  · exact redundant_of_reads_const n gs hs T hT j hj (n + k) hr
      (kc_const n gs hs T hT v hv b hb k (by omega) hK)
  · apply redundant_of_reads_const n gs hs T hT j hj (n + k) hr
    have hsk := (shaped_iff n gs).mp hs k (by omega)
    refine ⟨(gs[k]'(by omega)).op a b, fun x hx => ?_⟩
    rw [V_gate n x (hT x hx) gs k (by omega) (by omega) (by omega), hka, hkb]
    unfold V
    rw [run_getD_input _ _ _ (by rw [hT x hx]; exact hu),
      run_getD_input _ _ _ (by rw [hT x hx]; exact hv), ha x hx, hb x hx]

theorem elimCount_le (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (v : ℕ) (hv : v < n) (c : Bool) :
    elimCount n v c gs ≤ redCount n gs {x | x.length = n ∧ x.getD v false = c} := by
  classical
  unfold elimCount redCount
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨hj.1, elim_redundant n gs hs v hv c j hj.2⟩

theorem elim2Count_le (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (u v : ℕ) (hu : u < n)
    (hv : v < n) (a b : Bool) :
    elim2Count n u v a b gs ≤
      redCount n gs {x | x.length = n ∧ (x.getD u false = a ∧ x.getD v false = b)} := by
  classical
  unfold elim2Count redCount
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨hj.1, elim2_redundant n gs hs u v hu hv a b j hj.2⟩

/-! ### What the r-gate CNF says, in Lean -/

/-- **Everything the CNF for "an r-gate circuit computes MOD3^1_6" asserts**, `r = gs.length`,
with the r = 12 run's options (`best_opts`, `ELIM=1 ELIM2=1 SEM=1,2 SEMXOR=1 SYMIN=1 SEMEQ=1`,
and `cubes.py`'s table clause). -/
structure Admissible (gs : List Gate) (o : ℕ) (neg : Bool) : Prop where
  shaped : Shaped 6 gs
  normal : SymCanon.Normal gs
  out_lo : 6 ≤ o
  out_hi : o < 6 + gs.length
  computes : ComputesAt 6 (mod3 1) gs o neg
  nondegenerate : ∀ g ∈ gs,
    ¬ (g.op false true = false ∧ g.op true false = false ∧ g.op true true = false) ∧
    ¬ (g.op false true = false ∧ g.op true false = true ∧ g.op true true = true) ∧
    ¬ (g.op false true = true ∧ g.op true false = false ∧ g.op true true = true)
  used : ∀ j (h : j < gs.length), o = 6 + j ∨ ∃ k, ∃ hk : k < gs.length, j < k ∧ Reads gs[k] (6 + j)
  order : Order 6 gs
  symin : SymInOrd (· < 6) gs
  first01_table : ∀ h : 0 < gs.length, gs[0].a = 0 ∧ gs[0].b = 1 ∧ ¬ T100 gs[0]
  allin : AllIn 6 gs
  distinct : ∀ j < gs.length, ¬ Redundant 6 gs {x | x.length = 6} j
  elim : ∀ v < 6, ∀ c : Bool, elimCount 6 v c gs + c5 ((4 - c.toNat) % 3) ≤ gs.length
  elim2 : ∀ u < 6, ∀ v < 6, u < v → ∀ a b : Bool,
    elim2Count 6 u v a b gs + c4 ((7 - a.toNat - b.toNat) % 3) ≤ gs.length
  sem1 : ∀ v < 6, ∀ c : Bool,
    redCount 6 gs {x | x.length = 6 ∧ x.getD v false = c} + c5 ((4 - c.toNat) % 3) ≤ gs.length
  sem2 : ∀ u < 6, ∀ v < 6, u < v → ∀ a b : Bool,
    redCount 6 gs {x | x.length = 6 ∧ (x.getD u false = a ∧ x.getD v false = b)} +
      c4 ((7 - a.toNat - b.toNat) % 3) ≤ gs.length
  semxor : ∀ u < 6, ∀ v < 6, u < v →
    redCount 6 gs {x | x.length = 6 ∧ x.getD u false = (true ^^ x.getD v false)} + c4 0 ≤ gs.length
  semeq : ∀ u < 6, ∀ v < 6, u < v →
    redCount 6 gs {x | x.length = 6 ∧ x.getD u false = (false ^^ x.getD v false)} + 10 ≤ gs.length

/-! ### MOD3^1_6's own facts, by `decide` -/

theorem mod3_nonconst : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = 6 → mod3 1 x = c := by
  rintro ⟨c, h⟩
  have key : ∀ c : Bool, ∃ x ∈ allRows 6, mod3 1 x ≠ c := by decide +kernel
  obtain ⟨x, hx, hne⟩ := key c
  exact hne (h x (length_of_mem_allRows 6 x hx))

theorem mod3_nonlit :
    ¬ ∃ u < 6, ∃ b : Bool, ∀ x : List Bool, x.length = 6 → mod3 1 x = (b ^^ x.getD u false) := by
  rintro ⟨u, hu, b, h⟩
  have key : ∀ u < 6, ∀ b : Bool, ∃ x ∈ allRows 6, mod3 1 x ≠ (b ^^ x.getD u false) := by
    decide +kernel
  obtain ⟨x, hx, hne⟩ := key u hu b
  exact hne (h x (length_of_mem_allRows 6 x hx))

theorem mod3_essential : ∀ u < 6, ∃ x : List Bool, x.length = 6 ∧ mod3 1 (flipAt u x) ≠ mod3 1 x := by
  have key : ∀ u < 6, ∃ x ∈ allRows 6, mod3 1 (flipAt u x) ≠ mod3 1 x := by decide +kernel
  intro u hu
  obtain ⟨x, hx, hne⟩ := key u hu
  exact ⟨x, length_of_mem_allRows 6 x hx, hne⟩

/-! ### The lower bound -/

/-- **`size(MOD3^1_6) ≥ 13`, given that no `Admissible` circuit has ≤ 12 gates** (the SAT side)
and the smaller sizes `sem` uses. -/
theorem mod3_6_lower (h5 : ∀ q < 3, LB 5 (mod3 q) (c5 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw : LB 5 w2 10)
    (hsat : ∀ (gs : List Gate) (o : ℕ) (neg : Bool), gs.length ≤ 12 → Admissible gs o neg → False) :
    LB 6 (mod3 1) 13 := by
  classical
  intro gs hne hgs
  by_contra hlt
  have hex : ∃ m, ∃ gs : List Gate, BareComputes 6 (mod3 1) gs ∧ gs.length = m :=
    ⟨_, gs, ⟨hne, hgs⟩, rfl⟩
  obtain ⟨g0, hg0, hlen0⟩ := Nat.find_spec hex
  have hmin : ∀ gs', BareComputes 6 (mod3 1) gs' → g0.length ≤ gs'.length :=
    fun gs' h => hlen0 ▸ Nat.find_min' hex ⟨gs', h, rfl⟩
  have hle := hmin gs ⟨hne, hgs⟩
  obtain ⟨gs', neg, hl', hs', hn', hc', hO, hI, hF, hND, hAI, hNR, hbare, hblen⟩ :=
    minimal_canonical 6 (mod3 1) mod3_sym mod3_nonconst mod3_nonlit mod3_essential g0 hg0 hmin
  have hne' : gs' ≠ [] := by
    intro h; have := hg0.1; rw [h] at hl'; simp at hl'; exact this (List.length_eq_zero_iff.mp hl'.symm)
  have hpos : 0 < gs'.length := List.length_pos_of_ne_nil hne'
  obtain ⟨s1, s2, sx, se⟩ := mod3_6_1_sem_bounds h5 h4 hw _ hbare.1 hbare.2
  rw [hblen] at s1 s2 sx se
  have tr : ∀ T : Set (List Bool), (∀ x ∈ T, x.length = 6) →
      redCount 6 (toBare 6 gs' (6 + gs'.length - 1) neg) T = redCount 6 gs' T :=
    fun T hT => redCount_toBare 6 gs' neg hne' T hT
  have hshape := (shaped_iff 6 gs').mp hs'
  apply hsat gs' (6 + gs'.length - 1) neg (by omega)
  refine
    { shaped := hs', normal := hn', out_lo := by omega, out_hi := by omega, computes := hc',
      nondegenerate := ?_, used := ?_, order := hO, symin := hI, first01_table := hF,
      allin := hAI, distinct := hNR, elim := ?_, elim2 := ?_,
      sem1 := fun v hv c => by have := s1 v hv c; rwa [tr _ (fun x hx => hx.1)] at this,
      sem2 := fun u hu v hv huv a b => by
        have := s2 u hu v hv huv a b; rwa [tr _ (fun x hx => hx.1)] at this,
      semxor := fun u hu v hv huv => by have := sx u hu v hv huv; rwa [tr _ (fun x hx => hx.1)] at this,
      semeq := fun u hu v hv huv => by have := se u hu v hv huv; rwa [tr _ (fun x hx => hx.1)] at this }
  · -- `sym` (i): a degenerate table makes the gate `0`, `x_a` or `x_b`, which is redundant
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hsj := hshape j hj
    have hnorm := hn' _ hg
    have hT : ∀ x ∈ ({x | x.length = 6} : Set (List Bool)), x.length = 6 := fun x hx => hx
    have red : ∀ φ : Bool → Bool → Bool, (∀ p q, gs'[j].op p q = φ p q) →
        ((∀ p q, φ p q = false) ∨ (∀ p q, φ p q = p) ∨ (∀ p q, φ p q = q)) →
        Redundant 6 gs' {x | x.length = 6} j := by
      intro φ hφ hcase
      rcases hcase with h | h | h
      · exact Or.inl ⟨false, fun x hx => by
          rw [V_gate 6 x hx gs' j hj (by omega) (by omega), hφ, h]⟩
      · exact redundant_of_fun 6 gs' _ hT j gs'[j].a (by omega) id (fun x hx => by
          rw [V_gate 6 x hx gs' j hj (by omega) (by omega), hφ, h]; rfl)
      · exact redundant_of_fun 6 gs' _ hT j gs'[j].b (by omega) id (fun x hx => by
          rw [V_gate 6 x hx gs' j hj (by omega) (by omega), hφ, h]; rfl)
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs'[j].op (fun _ _ => rfl) (Or.inl fun p q => ?_))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs'[j].op (fun _ _ => rfl) (Or.inr (Or.inl fun p q => ?_)))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs'[j].op (fun _ _ => rfl) (Or.inr (Or.inr fun p q => ?_)))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
  · -- `sym` (ii): the output is the last gate, every other gate is read later
    intro j hj
    by_cases hlast : j + 1 < gs'.length
    · exact Or.inr (hND j hlast)
    · exact Or.inl (by omega)
  · intro v hv c
    have h1 := elimCount_le 6 gs' hs' v hv c
    have h2 := s1 v hv c
    rw [tr _ (fun x hx => hx.1)] at h2
    omega
  · intro u hu v hv huv a b
    have h1 := elim2Count_le 6 gs' hs' u v hu hv a b
    have h2 := s2 u hu v hv huv a b
    rw [tr _ (fun x hx => hx.1)] at h2
    omega

end Mod3Lower
