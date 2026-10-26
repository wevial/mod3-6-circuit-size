/-
# One `Admissible` for every run: a lower bound from a run's SAT side alone

`Mod3Lower.Admissible` is the r = 12 run's CNF in Lean. The smaller sizes it used (`CERTIFIED`,
`W2_LOWER`) are SAT results under other option sets. This file states every such run the same
way, so each smaller size can be proved from its own run instead of assumed.

* `Opts`: which clause families a run added. Every run had the encoding, `sym` and `order` and
  `distinct`; the rest are switches (`symin`, `table`, `first01`, `allin`) and bound tables
  (`elim`, `elim2`, and `sem` for every `redundancy(T, r − s)` clause: `sem`, `semxor`, `semeq`,
  `semrows`). A bound is stored as the size `s` it subtracts, so it does not depend on `r`.
* `Adm n f R gs o neg`: `gs` (output gate `o`, negated by `neg`) satisfies every clause family
  of the run `R` for `f`. One field per family, written as the clauses are; the table in
  `Mod3Lower`'s header maps fields to `optimal_circuit.encode`'s code.
* `NoAdm n f R lo hi`: no circuit of `lo` to `hi` gates satisfies `Adm n f R`. This is what a
  run certifies, given (as for `Mod3Lower`) that every `Adm` circuit of `r` gates satisfies the
  run's CNF for `r` (by eye) and the CNF is unsatisfiable (LRAT, outside the kernel).
* `Sound n f S R`: the run's symmetry breaks use the set `S`, and each of its `redundancy` bounds
  holds in every circuit for `f` (`SemOK`).

Proved (axioms: the standard three):
* `exists_adm`: for `f` symmetric in `S`, neither constant nor a literal, a minimum circuit has
  one of the same length satisfying `Adm n f R` for **every** sound run `R` at once.
* `lower`: so if, for each `r < s`, some sound run certifies that no `Adm` circuit has exactly
  `r` gates, then every circuit for `f` has at least `s` gates (`LB n f s`). `lower1`, `lower2`:
  the cases of one run, and of two runs split at a length.
-/
import Garden.Mod3Lower

namespace Tower
open CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds Mod3Lower

/-- The rows with `x_v = c`. -/
def rows1 (n v : ℕ) (c : Bool) : Set (List Bool) := {x | x.length = n ∧ x.getD v false = c}

/-- The rows with `x_u = a` and `x_v = b`. -/
def rows2 (n u v : ℕ) (a b : Bool) : Set (List Bool) :=
  {x | x.length = n ∧ (x.getD u false = a ∧ x.getD v false = b)}

/-- One run's clause families beyond the encoding, `sym`, `order` and `distinct`. -/
structure Opts where
  /-- the inputs `symin` (or `symvars`) and the table clause range over -/
  S : ℕ → Prop
  symin : Bool
  table : Bool
  first01 : Bool
  allin : Bool
  /-- `elim`: `B_c = r − e c` -/
  elim : Option (Bool → ℕ)
  /-- `elim2`: `B = r − e a b` for `x_u = a, x_v = b` -/
  elim2 : Option (Bool → Bool → ℕ)
  /-- `sem T s`: the run has the clause `redundancy(T, r − s)` -/
  sem : Set (List Bool) → ℕ → Prop

/-- **What a run's CNF asserts about `gs`**, `r = gs.length`, output gate `o` xor `neg`. -/
structure Adm (n : ℕ) (f : List Bool → Bool) (R : Opts) (gs : List Gate) (o : ℕ) (neg : Bool) :
    Prop where
  shaped : Shaped n gs
  normal : Normal gs
  out_lo : n ≤ o
  out_hi : o < n + gs.length
  computes : ComputesAt n f gs o neg
  nondegenerate : ∀ g ∈ gs,
    ¬ (g.op false true = false ∧ g.op true false = false ∧ g.op true true = false) ∧
    ¬ (g.op false true = false ∧ g.op true false = true ∧ g.op true true = true) ∧
    ¬ (g.op false true = true ∧ g.op true false = false ∧ g.op true true = true)
  used : ∀ j (_ : j < gs.length), o = n + j ∨ ∃ k, ∃ hk : k < gs.length, j < k ∧ Reads gs[k] (n + j)
  order : Order n gs
  distinct : ∀ j < gs.length, ¬ Redundant n gs {x | x.length = n} j
  symin : R.symin = true → SymInOrd R.S gs
  table : R.table = true → TableOK R.S gs
  first01 : R.first01 = true → ∀ h : 0 < gs.length, gs[0].a = 0 ∧ gs[0].b = 1
  allin : R.allin = true → ∀ u < n, Essential n f u → ∃ g ∈ gs, Reads g u
  elim : ∀ e, R.elim = some e → ∀ v < n, ∀ c : Bool, elimCount n v c gs + e c ≤ gs.length
  elim2 : ∀ e, R.elim2 = some e → ∀ u < n, ∀ v < n, u < v → ∀ a b : Bool,
    elim2Count n u v a b gs + e a b ≤ gs.length
  sem : ∀ T s, R.sem T s → redCount n gs T + s ≤ gs.length

/-- **What a run certifies**: no circuit of `lo` to `hi` gates satisfies `Adm n f R`. -/
def NoAdm (n : ℕ) (f : List Bool → Bool) (R : Opts) (lo hi : ℕ) : Prop :=
  ∀ (gs : List Gate) (o : ℕ) (neg : Bool), lo ≤ gs.length → gs.length ≤ hi → ¬ Adm n f R gs o neg

/-- The inequality of a `redundancy(T, r − s)` clause holds in every circuit computing `f`. -/
def SemOK (n : ℕ) (f : List Bool → Bool) (T : Set (List Bool)) (s : ℕ) : Prop :=
  (∀ x ∈ T, x.length = n) ∧
  ∀ gs : List Gate, gs ≠ [] → (∀ x : List Bool, x.length = n → out x gs = f x) →
    redCount n gs T + s ≤ gs.length

/-- The run's added constraints are sound for `f`, canonicalizing over `S`. -/
structure Sound (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (R : Opts) : Prop where
  S_eq : R.S = S
  first01 : R.first01 = true → ∀ u < n, S u
  sem : ∀ T s, R.sem T s → SemOK n f T s
  elim : ∀ e, R.elim = some e → ∀ v < n, ∀ c, SemOK n f (rows1 n v c) (e c)
  elim2 : ∀ e, R.elim2 = some e → ∀ u < n, ∀ v < n, u < v → ∀ a b,
    SemOK n f (rows2 n u v a b) (e a b)

lemma symin_mono (S S' : ℕ → Prop) (h : ∀ u, S' u → S u) (gs : List Gate) (hI : SymInOrd S gs) :
    SymInOrd S' gs :=
  fun u v hu hv => hI u v (h u hu) (h v hv)

/-- **A minimum circuit satisfies every sound run's `Adm` at once.** -/
theorem exists_adm (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (hS : ∀ u, S u → u < n)
    (hsym : SymOn n S f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (g0 : List Gate) (hg0 : BareComputes n f g0)
    (hmin : ∀ gs', BareComputes n f gs' → g0.length ≤ gs'.length) :
    ∃ gs o neg, gs.length = g0.length ∧ ∀ R, Sound n f S R → Adm n f R gs o neg := by
  classical
  obtain ⟨gs', neg, hl', hs', hn', hc', hO, hI, hT, hND, hAI, hNR, hbare, hblen⟩ :=
    minimal_canonical_on n f S hS hsym hc hl g0 hg0 hmin
  have hne' : gs' ≠ [] := by
    intro h; rw [h] at hl'; exact hg0.1 (List.length_eq_zero_iff.mp hl'.symm)
  have hpos : 0 < gs'.length := List.length_pos_of_ne_nil hne'
  have hshape := (shaped_iff n gs').mp hs'
  -- a sound `redundancy` bound, moved from `toBare` to the shaped circuit
  have semgs : ∀ T s, SemOK n f T s → redCount n gs' T + s ≤ gs'.length := by
    rintro T s ⟨hT, h⟩
    have := h _ hbare.1 hbare.2
    rwa [hblen, redCount_toBare n gs' neg hne' T hT] at this
  refine ⟨gs', n + gs'.length - 1, neg, hl', fun R hR => ?_⟩
  refine
    { shaped := hs', normal := hn', out_lo := by omega, out_hi := by omega, computes := hc',
      nondegenerate := ?_, used := ?_, order := hO, distinct := hNR,
      symin := fun _ => by rw [hR.S_eq]; exact hI,
      table := fun _ => by rw [hR.S_eq]; exact hT,
      first01 := fun h01 h => first01_of_symin n gs' hs'
        (symin_mono S (· < n) (fun u hu => hR.first01 h01 u hu) gs' hI) h,
      allin := fun _ => hAI,
      elim := fun e he v hv c => by
        have h1 := elimCount_le n gs' hs' v hv c
        have h2 := semgs _ _ (hR.elim e he v hv c)
        unfold rows1 at h2; omega,
      elim2 := fun e he u hu v hv huv a b => by
        have h1 := elim2Count_le n gs' hs' u v hu hv a b
        have h2 := semgs _ _ (hR.elim2 e he u hu v hv huv a b)
        unfold rows2 at h2; omega,
      sem := fun T s h => semgs T s (hR.sem T s h) }
  · -- `sym` (i): a degenerate table makes the gate `0`, `x_a` or `x_b`, which is redundant
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hsj := hshape j hj
    have hnorm := hn' _ hg
    have hT : ∀ x ∈ ({x | x.length = n} : Set (List Bool)), x.length = n := fun x hx => hx
    have red : ∀ φ : Bool → Bool → Bool, (∀ p q, gs'[j].op p q = φ p q) →
        ((∀ p q, φ p q = false) ∨ (∀ p q, φ p q = p) ∨ (∀ p q, φ p q = q)) →
        Redundant n gs' {x | x.length = n} j := by
      intro φ hφ hcase
      rcases hcase with h | h | h
      · exact Or.inl ⟨false, fun x hx => by
          rw [V_gate n x hx gs' j hj (by omega) (by omega), hφ, h]⟩
      · exact redundant_of_fun n gs' _ hT j gs'[j].a (by omega) id (fun x hx => by
          rw [V_gate n x hx gs' j hj (by omega) (by omega), hφ, h]; rfl)
      · exact redundant_of_fun n gs' _ hT j gs'[j].b (by omega) id (fun x hx => by
          rw [V_gate n x hx gs' j hj (by omega) (by omega), hφ, h]; rfl)
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

/-- **A lower bound from the runs alone.** If for every `r` with `1 ≤ r < s` a sound run `R r`
certifies that no circuit of exactly `r` gates satisfies its `Adm`, then `size(f) ≥ s`. -/
theorem lower (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (hS : ∀ u, S u → u < n)
    (hsym : SymOn n S f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (s : ℕ) (R : ℕ → Opts) (hR : ∀ r, 1 ≤ r → r < s → Sound n f S (R r))
    (hsat : ∀ r, 1 ≤ r → r < s → ∀ gs o neg, gs.length = r → ¬ Adm n f (R r) gs o neg) :
    LB n f s := by
  classical
  intro gs hne hgs
  by_contra hlt
  have hex : ∃ m, ∃ gs : List Gate, BareComputes n f gs ∧ gs.length = m :=
    ⟨_, gs, ⟨hne, hgs⟩, rfl⟩
  obtain ⟨g0, hg0, hlen0⟩ := Nat.find_spec hex
  have hmin : ∀ gs', BareComputes n f gs' → g0.length ≤ gs'.length :=
    fun gs' h => hlen0 ▸ Nat.find_min' hex ⟨gs', h, rfl⟩
  have hle := hmin gs ⟨hne, hgs⟩
  have hpos : 1 ≤ g0.length := List.length_pos_of_ne_nil hg0.1
  obtain ⟨gs', o, neg, hl', hadm⟩ := exists_adm n f S hS hsym hc hl g0 hg0 hmin
  exact hsat g0.length hpos (by omega) gs' o neg hl' (hadm _ (hR _ hpos (by omega)))

/-- One run covering every length below `s`. -/
theorem lower1 (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (hS : ∀ u, S u → u < n)
    (hsym : SymOn n S f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (R : Opts) (hR : Sound n f S R) (s : ℕ) (h : NoAdm n f R 1 (s - 1)) : LB n f s :=
  lower n f S hS hsym hc hl s (fun _ => R) (fun _ _ _ => hR)
    (fun _ h1 h2 gs o neg hl' => h gs o neg (by omega) (by omega))

/-- Two runs: `R1` for lengths `1 … a`, `R2` for `a + 1 … s − 1`. -/
theorem lower2 (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (hS : ∀ u, S u → u < n)
    (hsym : SymOn n S f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (R1 R2 : Opts) (hR1 : Sound n f S R1) (hR2 : Sound n f S R2) (a s : ℕ)
    (h1 : NoAdm n f R1 1 a) (h2 : NoAdm n f R2 (a + 1) (s - 1)) : LB n f s :=
  lower n f S hS hsym hc hl s (fun r => if r ≤ a then R1 else R2)
    (fun r _ _ => by split_ifs; exacts [hR1, hR2])
    (fun r hr1 hr2 gs o neg hl' => by
      split_ifs with h
      · exact h1 gs o neg (by omega) (by omega)
      · exact h2 gs o neg (by omega) (by omega))

/-- Two runs with the same options on adjacent length ranges are one range. -/
lemma noAdm_join (n : ℕ) (f : List Bool → Bool) (R : Opts) (a b c : ℕ) (h1 : NoAdm n f R a b)
    (h2 : NoAdm n f R (b + 1) c) : NoAdm n f R a c := by
  intro gs o neg hlo hhi
  by_cases h : gs.length ≤ b
  · exact h1 gs o neg hlo h
  · exact h2 gs o neg (by omega) hhi

/-! ### The finite facts each instance needs, from a check over `allRows` -/

lemma nonconst_of (n : ℕ) (f : List Bool → Bool) (h : ∀ c : Bool, ∃ x ∈ allRows n, f x ≠ c) :
    ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, hne⟩ := h c
  exact hne (hc x (length_of_mem_allRows n x hx))

lemma nonlit_of (n : ℕ) (f : List Bool → Bool)
    (h : ∀ u < n, ∀ b : Bool, ∃ x ∈ allRows n, f x ≠ (b ^^ x.getD u false)) :
    ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false) := by
  rintro ⟨u, hu, b, hb⟩
  obtain ⟨x, hx, hne⟩ := h u hu b
  exact hne (hb x (length_of_mem_allRows n x hx))

lemma symOn_of (n : ℕ) (S : ℕ → Prop) (hS : ∀ u, S u → u < n) (f : List Bool → Bool)
    (h : ∀ u < n, ∀ v < n, S u → S v → ∀ z ∈ allRows n, f (swapIn u v z) = f z) : SymOn n S f :=
  fun u v hu hv x hx => h u (hS u hu) v (hS v hv) hu hv x (mem_allRows x n hx)

/-- A `redundancy` bound from a substitution pattern, every side condition a finite check:
the rows `cond` are the image of `sig p`, and `f ∘ sig p` is neither constant nor a literal and
needs `s` gates. -/
lemma semOK_of (n m : ℕ) (p : List Rep) (f : List Bool → Bool) (cond : List Bool → Prop)
    (proj : List Bool → List Bool) (s : ℕ)
    (hA : ∀ y ∈ allRows m, cond (inRow n (sig p) y))
    (hB : ∀ x ∈ allRows n, cond x → (proj x).length = m ∧ x = inRow n (sig p) (proj x))
    (hσ : ∀ i < n, (sig p i).Lt m)
    (hc : ∀ c : Bool, ∃ y ∈ allRows m, f (inRow n (sig p) y) ≠ c)
    (hl : ∀ k < m, ∀ b : Bool, ∃ y ∈ allRows m, f (inRow n (sig p) y) ≠ (b ^^ y.getD k false))
    (hlb : LB m (fun y => f (inRow n (sig p) y)) s) :
    SemOK n f {x | x.length = n ∧ cond x} s := by
  rw [set_eq n m _ cond proj hA hB]
  refine ⟨by rintro x ⟨y, -, rfl⟩; exact inRow_length _ _ _, fun gs hne hgs => ?_⟩
  exact bound_of_pattern n m p f s hσ hc hl hlb gs hne hgs

/-- A run with none of the switches or bounds is sound for any `f`, given its `S`. -/
lemma sound_plain (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop) (R : Opts) (hS : R.S = S)
    (h01 : R.first01 = true → ∀ u < n, S u) (hsem : ∀ T s, ¬ R.sem T s) (he : R.elim = none)
    (he2 : R.elim2 = none) : Sound n f S R where
  S_eq := hS
  first01 := h01
  sem := fun T s h => absurd h (hsem T s)
  elim := fun e h => by rw [he] at h; cases h
  elim2 := fun e h => by rw [he2] at h; cases h

end Tower
