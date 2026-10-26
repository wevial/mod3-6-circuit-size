import Garden.CnfSpecs
import Garden.CnfSound
import Garden.Mod3Tower
import Garden.Mod3Upper

/-!
# size(MOD3^1_6) = size(MOD3^2_6) = 13, from the unsatisfiability of Lean-generated CNFs

`Mod3Tower.mod3_6_lower_sat` proves `size ≥ 13` from 22 hypotheses `NoAdm …`, one per SAT run,
each saying no circuit with the run's number of gates satisfies the run's `Adm`. Until now each
was tied to the run's CNF by eye. Here the CNFs themselves are the hypotheses: `CnfGen`
generates each run's CNF (a transcription of `optimal_circuit.encode` and `cubes.py`; every leaf is
byte-identical to the DIMACS its ledger hashed, and every scan CNF is re-solved from the export), and
`CnfSound.adm_sat` proves that every `Adm` circuit satisfies it. So:

* `ScanUnsat R lo hi`: the run `R`'s CNF is unsatisfiable for every `r` from `lo` to `hi`;
  `LeavesUnsat R r ls`: every leaf CNF of a split run is. Both are statements about
  `Std.Sat.CNF Nat`, the type `lratcheck`'s verified checker concludes `Unsat` for
  (`Garden.LratStream.runChunks_sound`).
* `noAdm_scan`, `noAdm_leaves`: each gives the run's `NoAdm`. For split runs this needs the
  cover: every `Adm` circuit lies in some leaf's cube (`cover5`, `coverW2`, `cover12`).
* **`mod3_6_size_13`**: from the 22 hypotheses (one per run), both functions have size exactly 13
  (the upper bound is `Mod3Upper`'s circuit).
* `mod3_6_size_13_lists`: the same, with the hypotheses read off `CnfSpecs.scanList` and
  `splitList`, the lists `cnfexport` and `cnf_certify.py` iterate.
* `cnf13_sat` (positive control): under the same hypotheses, the r = 13 CNF of the full
  encoding is satisfiable. It is conditional. Outside Lean, `cnf_certify.py` checks the
  unconditional fact behind it: Lean's r = 13 CNF of the cube that came back SAT is that ledger
  line's DIMACS, and its recorded model satisfies every clause, so the encoding has a solution
  where a 13-gate circuit exists. That the hypotheses hold (hence are consistent) is the
  certification itself.
* `leafCnf_split`, `dimacs_append`: a leaf's CNF is its base's followed by the cube's unit
  clauses, and its DIMACS is a header, the base's body, the cube's lines. `cnf_certify.py` hashes
  leaves that way.

`research/circuits/cnf_certify.py` (output `cnf_certify.out`) certifies every hypothesis: each
split run's leaves are byte-identical (sha256) to DIMACS files a ledger records as refuted with
a proof `lratcheck` accepted, and each scan's CNFs are re-solved from the Lean export by CaDiCaL
with `lratcheck`. Axioms: the standard three.
-/

namespace CnfRuns
open CnfGen CnfSound CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds Mod3Lower
  Tower W2SemBounds

/-! ### A leaf's CNF and DIMACS, in pieces -/

def setOut (s : NS) (X : Array (List Int)) : NS := { s with out := X }

lemma declare_setOut (s : NS) (X : Array (List Int)) (m : M) :
    (setOut s X).declare m = setOut (s.declare m) X := rfl

lemma declare_out (s : NS) (m : M) : (s.declare m).out = s.out := rfl

lemma lit_setOut (s : NS) (X : Array (List Int)) (l : L) :
    (setOut s X).lit l = (setOut (s.lit l).1 X, (s.lit l).2) := by
  cases h : s.map[l.1]? <;> simp only [NS.lit, setOut, h] <;> rfl

lemma lit_out (s : NS) (l : L) : (s.lit l).1.out = s.out := by
  cases h : s.map[l.1]? <;> simp only [NS.lit, h] <;> rfl

lemma lits_setOut : ∀ (c : List L) (s : NS) (X : Array (List Int)),
    (setOut s X).lits c = (setOut (s.lits c).1 X, (s.lits c).2)
  | [], s, X => rfl
  | l :: ls, s, X => by
    have h1 : (setOut s X).lits (l :: ls) = ((((setOut s X).lit l).1.lits ls).1,
        ((setOut s X).lit l).2 :: (((setOut s X).lit l).1.lits ls).2) := rfl
    have h2 : s.lits (l :: ls) = (((s.lit l).1.lits ls).1, (s.lit l).2 :: ((s.lit l).1.lits ls).2) := rfl
    simp only [h1, h2, lit_setOut, lits_setOut ls]

lemma lits_out : ∀ (c : List L) (s : NS), (s.lits c).1.out = s.out
  | [], s => rfl
  | l :: ls, s => by
    have h2 : s.lits (l :: ls) = (((s.lit l).1.lits ls).1, (s.lit l).2 :: ((s.lit l).1.lits ls).2) := rfl
    rw [h2, lits_out ls, lit_out]

lemma clause_eq (s : NS) (c : List L) :
    s.clause c = { (s.lits c).1 with out := (s.lits c).1.out.push (s.lits c).2 } := rfl

lemma clause_shift (s : NS) (A : Array (List Int)) (c : List L) :
    (setOut s (A ++ s.out)).clause c = setOut (s.clause c) (A ++ (s.clause c).out) := by
  rw [clause_eq, clause_eq, lits_setOut]
  simp only [setOut, lits_out, Array.append_push]

lemma clauses_shift : ∀ (ds : List (List L)) (s : NS) (A : Array (List Int)),
    ds.foldl NS.clause (setOut s (A ++ s.out)) = setOut (ds.foldl NS.clause s) (A ++ (ds.foldl NS.clause s).out)
  | [], s, A => rfl
  | d :: ds, s, A => by
    simp only [List.foldl_cons]
    rw [clause_shift, clauses_shift ds]

lemma step_shift (s : NS) (A : Array (List Int)) (e : Ev) :
    (setOut s (A ++ s.out)).step e = setOut (s.step e) (A ++ (s.step e).out) := by
  cases e with
  | decl m => rfl
  | cl c => exact clause_shift s A c
  | lazy m defs =>
    simp only [NS.step]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rw [declare_setOut, ← declare_out s m, clauses_shift]

lemma foldl_shift : ∀ (evs : List Ev) (s : NS) (A : Array (List Int)),
    evs.foldl NS.step (setOut s (A ++ s.out)) = setOut (evs.foldl NS.step s) (A ++ (evs.foldl NS.step s).out)
  | [], s, A => rfl
  | e :: es, s, A => by
    simp only [List.foldl_cons]
    rw [step_shift, foldl_shift es]

/-- **A leaf's CNF is its base's, then the cube's unit clauses** (what `cnfexport leaves` writes). -/
theorem leafCnf_split (R : CnfSpecs.Run) (r : ℕ) (cube : List L) :
    R.leafCnf r cube = R.cnf r ++ CnfSpecs.cubeCnf (number (events R.n r R.tt R.o)) cube := by
  unfold CnfSpecs.Run.leafCnf CnfSpecs.Run.cnf CnfSpecs.cubeCnf cnfOf number
  rw [List.foldl_append]
  set b := (events R.n r R.tt R.o).foldl NS.step {}
  have hb : b = setOut { b with out := #[] } (b.out ++ ({ b with out := #[] } : NS).out) := by
    simp [setOut]
  conv_lhs => rw [hb, foldl_shift]
  simp [setOut]

lemma foldl_max (F : List ℕ) (m : ℕ) : F.foldl max m = max m (F.foldl max 0) := by
  induction F generalizing m with
  | nil => simp
  | cons a F ih => simp only [List.foldl_cons]; rw [ih, ih (max 0 a)]; omega

lemma inner_max (c : List ℤ) (m : ℕ) :
    c.foldl (fun m l => max m l.natAbs) m = max m (c.foldl (fun m l => max m l.natAbs) 0) := by
  induction c generalizing m with
  | nil => simp
  | cons a c ih => simp only [List.foldl_cons]; rw [ih, ih (max 0 a.natAbs)]; omega

lemma outer_max (F : List (List ℤ)) (m : ℕ) :
    F.foldl (fun m c => c.foldl (fun m l => max m l.natAbs) m) m = max m (maxVar F) := by
  unfold maxVar
  induction F generalizing m with
  | nil => simp
  | cons c F ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (c.foldl _ 0), inner_max c m]; omega

lemma maxVar_append (A B : List (List ℤ)) : maxVar (A ++ B) = max (maxVar A) (maxVar B) := by
  conv_lhs => unfold maxVar
  rw [List.foldl_append, outer_max]; rfl

lemma body_append (A B : List (List ℤ)) : body (A ++ B) = body A ++ body B := by
  unfold body
  rw [List.map_append]
  induction A with
  | nil => simp
  | cons c A ih => simp only [List.map_cons, List.cons_append, String.join_cons, ih, String.append_assoc]

/-- **A concatenation's DIMACS**: header, then the two bodies. -/
theorem dimacs_append (A B : List (List ℤ)) :
    dimacs (A ++ B) = header (max (maxVar A) (maxVar B)) (A.length + B.length) ++ body A ++ body B := by
  unfold dimacs
  rw [maxVar_append, List.length_append, body_append, String.append_assoc]

/-! ### The hypotheses' form -/

/-- **A scan's SAT side**: the run's Lean-generated CNF is unsatisfiable for every `r ∈ [lo, hi]`. -/
def ScanUnsat (R : CnfSpecs.Run) (lo hi : ℕ) : Prop :=
  ∀ r, lo ≤ r → r ≤ hi → (toCNF (R.cnf r)).Unsat

/-- **A split run's SAT side**: every leaf's Lean-generated CNF is unsatisfiable. -/
def LeavesUnsat (R : ℕ → CnfSpecs.Run) (r : ℕ) (ls : List CnfSpecs.Leaf) : Prop :=
  ∀ L ∈ ls, (toCNF ((R L.tag).leafCnf r L.cube)).Unsat

theorem noAdm_scan (n : ℕ) (f : List Bool → Bool) (R : Opts) (tt : ℕ → Bool) (o : EOpts)
    (htt : ∀ t < 2 ^ n, tt t = f (row n t)) (hF : Fits n R o) (lo hi : ℕ)
    (h : ScanUnsat ⟨n, tt, o⟩ lo hi) : NoAdm n f R lo hi := by
  intro gs ou neg hlo hhi hadm
  apply adm_sat n f R gs ou neg hadm tt htt o hF [] (by simp)
  simpa [CnfSpecs.Run.cnf] using h gs.length hlo hhi

theorem noAdm_leaves (n : ℕ) (f : List Bool → Bool) (R : Opts) (tt : ℕ → Bool) (o : ℕ → EOpts)
    (htt : ∀ t < 2 ^ n, tt t = f (row n t)) (hF : ∀ g, Fits n R (o g)) (r : ℕ)
    (ls : List CnfSpecs.Leaf)
    (hcov : ∀ gs ou neg, Adm n f R gs ou neg → gs.length = r →
      ∃ L ∈ ls, ∀ l ∈ L.cube, ev n gs ou neg l.1 = l.2)
    (h : LeavesUnsat (fun g => ⟨n, tt, o g⟩) r ls) : NoAdm n f R r r := by
  intro gs ou neg hlo hhi hadm
  have hlen : gs.length = r := by omega
  obtain ⟨L, hL, hc⟩ := hcov gs ou neg hadm hlen
  apply adm_sat n f R gs ou neg hadm tt htt (o L.tag) (hF L.tag) L.cube hc
  rw [hlen]; exact h L hL

/-! ### Truth tables: `tt_of` is the Lean function -/

set_option maxRecDepth 4000 in
theorem tt_facts :
    (∀ q < 3, ∀ t < 2 ^ 3, CnfSpecs.mod3T q 3 t = mod3 q (row 3 t)) ∧
    (∀ q < 3, ∀ t < 2 ^ 4, CnfSpecs.mod3T q 4 t = mod3 q (row 4 t)) ∧
    (∀ q < 3, ∀ t < 2 ^ 5, CnfSpecs.mod3T q 5 t = mod3 q (row 5 t)) ∧
    (∀ t < 2 ^ 6, CnfSpecs.mod3T 1 6 t = mod3 1 (row 6 t)) ∧
    (∀ q < 3, ∀ t < 2 ^ 3, CnfSpecs.wqT q 3 t = wq q (row 3 t)) ∧
    (∀ q < 2, ∀ t < 2 ^ 4, CnfSpecs.wqT q 4 t = wq q (row 4 t)) ∧
    (∀ t < 2 ^ 4, CnfSpecs.pqT t = pq (row 4 t)) ∧
    (∀ t < 2 ^ 5, CnfSpecs.wqT 1 5 t = w2 (row 5 t)) := by
  decide +kernel

/-! ### Each run's encoder options fit its `Opts` -/

lemma rowSet_eq (n : ℕ) (p : ℕ → Bool) (P : List Bool → Prop)
    (hp : ∀ t < 2 ^ n, p t = true ↔ P (row n t)) :
    rowSet n (CnfSpecs.rowsWhere n p) = {x | x.length = n ∧ P x} :=
  rowSet_where n p P hp

lemma mem_sem1Rows (n : ℕ) (s : ℕ → Bool → ℕ) (x : List ℕ × ℕ) (hx : x ∈ CnfSpecs.sem1Rows n s) :
    ∃ v < n, ∃ c : Bool, x = (CnfSpecs.rowsWhere n fun t => t.testBit v == c, s v c) := by
  simp only [CnfSpecs.sem1Rows, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hx
  obtain ⟨v, hv, c, -, rfl⟩ := hx
  exact ⟨v, hv, c, rfl⟩

lemma pair_of_combs (n : ℕ) (c : List ℕ) (hc : c ∈ combs 2 (List.range n)) :
    ∃ u v, c = [u, v] ∧ u < v ∧ v < n := by
  obtain ⟨u, v, rfl, hsub⟩ := mem_combs2 _ c hc
  exact ⟨u, v, rfl, sublist_pair_lt _ List.pairwise_lt_range u v hsub,
    List.mem_range.mp (hsub.subset (by simp))⟩

lemma mem_sem2Rows (n : ℕ) (s : ℕ → Bool → Bool → ℕ) (x : List ℕ × ℕ)
    (hx : x ∈ CnfSpecs.sem2Rows n s) : ∃ u v, u < v ∧ v < n ∧ ∃ a b : Bool,
      x = (CnfSpecs.rowsWhere n fun t => t.testBit u == a && t.testBit v == b, s u a b) := by
  simp only [CnfSpecs.sem2Rows, List.mem_flatMap] at hx
  obtain ⟨c, hc, hx⟩ := hx
  obtain ⟨u, v, rfl, huv, hv⟩ := pair_of_combs n c hc
  simp only [List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  obtain ⟨⟨a, b⟩, -, rfl⟩ := hx
  exact ⟨u, v, huv, hv, a, b, rfl⟩

lemma mem_pairRows (n : ℕ) (cs : List Bool) (s : ℕ → Bool → ℕ) (x : List ℕ × ℕ)
    (hx : x ∈ CnfSpecs.pairRows n cs s) : ∃ u v, u < v ∧ v < n ∧ ∃ c ∈ cs,
      x = (CnfSpecs.rowsWhere n fun t => (t.testBit u ^^ t.testBit v) == c, s u c) := by
  simp only [CnfSpecs.pairRows, List.mem_flatMap] at hx
  obtain ⟨c, hc, hx⟩ := hx
  obtain ⟨u, v, rfl, huv, hv⟩ := pair_of_combs n c hc
  simp only [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨u, v, huv, hv, c, hc, rfl⟩

lemma rows1_eq (n v : ℕ) (hv : v < n) (c : Bool) :
    rowSet n (CnfSpecs.rowsWhere n fun t => t.testBit v == c) = rows1 n v c :=
  rowSet_eq n _ _ fun t _ => by rw [row_getD n t v hv]; simp

lemma rows2_eq (n u v : ℕ) (hu : u < n) (hv : v < n) (a b : Bool) :
    rowSet n (CnfSpecs.rowsWhere n fun t => t.testBit u == a && t.testBit v == b) = rows2 n u v a b :=
  rowSet_eq n _ _ fun t _ => by rw [row_getD n t u hu, row_getD n t v hv]; simp

lemma rowsX_eq (n u v : ℕ) (hu : u < n) (hv : v < n) (c : Bool) (P : Bool → Bool → Prop)
    (hP : ∀ a b : Bool, ((a ^^ b) == c) = true ↔ P a b) :
    rowSet n (CnfSpecs.rowsWhere n fun t => (t.testBit u ^^ t.testBit v) == c) =
      {x | x.length = n ∧ P (x.getD u false) (x.getD v false)} :=
  rowSet_eq n _ _ fun t _ => by rw [row_getD n t u hu, row_getD n t v hv]; exact hP _ _

theorem fits_best (n : ℕ) : Fits n (Mod3Tower.best n) CnfSpecs.bestO where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := fun _ h => by cases h
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun h => by cases h

theorem fits_cube5 : Fits 5 Mod3Tower.cube5 CnfSpecs.cube5O where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := fun _ h => by cases h
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun _ => ⟨rfl, fun _ h => h⟩

theorem fits_restr (n : ℕ) : Fits n Mod3Tower.restr CnfSpecs.restrO where
  first01 := fun h => by cases h
  allin := fun h => by cases h
  elim := fun _ h => by cases h
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun h => by cases h

theorem fits_w2best : Fits 5 Mod3Tower.w2best CnfSpecs.w2bestO where
  first01 := fun h => by cases h
  allin := fun _ => rfl
  elim := fun _ h => by cases h
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun h => by cases h

theorem fits_elim6 : Fits 6 Mod3Tower.elim6 CnfSpecs.elim6O where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := fun s h => by
    cases h; exact ⟨fun c => Mod3SemBounds.c5 ((4 - c.toNat) % 3), rfl, by decide, by decide⟩
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun h => by cases h

theorem fits_full6 (S E : Bool) : Fits 6 Mod3Tower.full6 (CnfSpecs.full6O S E) where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := fun s h => by
    cases h; exact ⟨fun c => Mod3SemBounds.c5 ((4 - c.toNat) % 3), rfl, by decide, by decide⟩
  elim2 := fun s h => by
    cases h
    exact ⟨fun a b => Mod3SemBounds.c4 ((7 - a.toNat - b.toNat) % 3), rfl, by decide⟩
  red := by
    intro x hx _
    simp only [CnfSpecs.full6O, CnfSpecs.red6, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · obtain ⟨v, hv, c, rfl⟩ := mem_sem1Rows _ _ x hx
      exact ⟨_, Or.inl ⟨v, hv, c, rows1_eq 6 v hv c, rfl⟩, le_refl _⟩
    · obtain ⟨u, v, huv, hv, a, b, rfl⟩ := mem_sem2Rows _ _ x hx
      exact ⟨_, Or.inr (Or.inl ⟨u, by omega, v, hv, huv, a, b, rows2_eq 6 u v (by omega) hv a b,
        rfl⟩), le_refl _⟩
    · obtain ⟨u, v, huv, hv, c, hc, rfl⟩ := mem_pairRows _ _ _ x hx
      simp only [List.mem_singleton] at hc; subst hc
      refine ⟨_, Or.inr (Or.inr (Or.inl ⟨u, by omega, v, hv, huv,
        rowsX_eq 6 u v (by omega) hv true (fun a b => a = (true ^^ b))
          (fun a b => by cases a <;> cases b <;> simp), rfl⟩)),
        le_refl _⟩
    · split_ifs at hx
      · obtain ⟨u, v, huv, hv, c, hc, rfl⟩ := mem_pairRows _ _ _ x hx
        simp only [List.mem_singleton] at hc; subst hc
        refine ⟨_, Or.inr (Or.inr (Or.inr ⟨u, by omega, v, hv, huv,
          rowsX_eq 6 u v (by omega) hv false (fun a b => a = (false ^^ b))
            (fun a b => by cases a <;> cases b <;> simp), rfl⟩)),
          le_refl _⟩
      · simp at hx
  symin := fun _ => ⟨rfl, fun _ h => h⟩
  symvars := fun _ h => by cases h
  table := fun _ => ⟨rfl, fun _ h => h⟩

theorem fits_w2cube : Fits 5 Mod3Tower.w2cube CnfSpecs.w2cubeO where
  first01 := fun h => by cases h
  allin := fun _ => rfl
  elim := fun _ h => by cases h
  elim2 := fun _ h => by cases h
  red := by
    intro x hx _
    simp only [CnfSpecs.w2cubeO, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨v, hv, c, rfl⟩ := mem_sem1Rows _ _ x hx
      exact ⟨_, Or.inl (Or.inl ⟨v, hv, c, rows1_eq 5 v hv c, rfl⟩), le_refl _⟩
    · obtain ⟨u, v, huv, hv, a, b, rfl⟩ := mem_sem2Rows _ _ x hx
      exact ⟨_, Or.inl (Or.inr ⟨u, by omega, v, hv, huv, a, b, rows2_eq 5 u v (by omega) hv a b,
        rfl⟩), le_refl _⟩
    · obtain ⟨u, v, huv, hv, c, -, rfl⟩ := mem_pairRows _ _ _ x hx
      refine ⟨_, Or.inr ⟨u, by omega, v, hv, huv, c,
        rowsX_eq 5 u v (by omega) hv c (fun a b => b = (c ^^ a))
          (fun a b => by cases a <;> cases b <;> cases c <;> simp), rfl⟩, le_refl _⟩
  symin := fun h => by cases h
  symvars := fun S h => by
    cases h
    refine ⟨rfl, rfl, fun u hu => ?_, by decide⟩
    show 1 ≤ u ∧ u < 5
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
    omega
  table := fun h => by cases h

/-! ### Covers: every `Adm` circuit lies in some leaf

Proved once for the generic tree (`tree_cover`): if the cube so far holds and every remaining
level has a choice that holds, some leaf below holds. The data (which nodes are split, which
ledger certifies a leaf) never enters the proof. Each run then needs only one fact per level:
the circuit's first table is one of the table cubes, and each gate's pair is one of its pairs. -/

lemma getD_of_mem {α : Type} (L : List α) (x d : α) (h : x ∈ L) : ∃ k < L.length, L.getD k d = x := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, hk, by simp [List.getD_eq_getElem?_getD, hk]⟩

/-- **The cover, for any tree.** -/
theorem tree_cover (P : L → Prop) (tagF : ℕ → ℕ → Option ℕ) (dflt : ℕ) :
    ∀ (levels : List (List (List L))) (d p : ℕ) (c : List L), (∀ l ∈ c, P l) →
      (∀ lv ∈ levels, ∃ ch ∈ lv, ∀ l ∈ ch, P l) →
      ∃ Lf ∈ CnfSpecs.tree tagF dflt d levels p c, ∀ l ∈ Lf.cube, P l
  | [], d, p, c, hc, _ => ⟨⟨(tagF d p).getD dflt, d, p, c⟩, by simp [CnfSpecs.tree], hc⟩
  | lv :: rest, d, p, c, hc, hl => by
    rcases h : tagF d p with _ | g
    · obtain ⟨ch, hch, hP⟩ := hl lv (List.mem_cons_self ..)
      obtain ⟨i, hi, hget⟩ := getD_of_mem lv ch [] hch
      obtain ⟨Lf, hLf, hP'⟩ := tree_cover P tagF dflt rest (d + 1) (p * lv.length + i)
        (c ++ lv.getD i []) (by rw [hget]; intro l hl'; rw [List.mem_append] at hl'
                                rcases hl' with hl' | hl' <;> [exact hc l hl'; exact hP l hl'])
        (fun lv' h' => hl lv' (List.mem_cons_of_mem _ h'))
      refine ⟨Lf, ?_, hP'⟩
      simp only [CnfSpecs.tree, h, List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hLf⟩
    · exact ⟨⟨g, d, p, c⟩, by simp [CnfSpecs.tree, h], hc⟩

section Cover
variable (n : ℕ) (gs : List Gate) (ou : ℕ) (neg : Bool)

/-- The first gate's table bits. -/
def bits (i : ℕ) : Bool × Bool × Bool :=
  ((gt n gs i).op false true, (gt n gs i).op true false, (gt n gs i).op true true)

lemma tableCube_true (i : ℕ) : ∀ l ∈ CnfSpecs.tableCube i (bits n gs i), ev n gs ou neg l.1 = l.2 := by
  simp [CnfSpecs.tableCube, bits, ev]

/-- Gate `i`'s pair level has a true choice. -/
lemma pairLevel_true (hs : Shaped n gs) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + gs.length) :
    ∃ ch ∈ CnfSpecs.pairLevel i, ∀ l ∈ ch, ev n gs ou neg l.1 = l.2 := by
  obtain ⟨h1, h2, -⟩ := nodeV_gate n gs hs i hi1 hi2 0
  refine ⟨[CnfSpecs.pairLit i ((gt n gs i).a, (gt n gs i).b)],
    List.mem_map.mpr ⟨_, (mem_pairs _ _).mpr ⟨h1, h2⟩, rfl⟩, ?_⟩
  simp [CnfSpecs.pairLit, pos, ev]

/-- The table level has a true choice, given that `bits` is one of its tables. -/
lemma tableLevel_true (ts : List (Bool × Bool × Bool)) (h : bits n gs n ∈ ts) :
    ∃ ch ∈ CnfSpecs.tableLevel n ts, ∀ l ∈ ch, ev n gs ou neg l.1 = l.2 :=
  ⟨_, List.mem_map.mpr ⟨_, h, rfl⟩, tableCube_true n gs ou neg n⟩

lemma bits_mem5 (f : List Bool → Bool) (R : Opts) (h : Adm n f R gs ou neg) (hpos : 0 < gs.length) :
    bits n gs n ∈ CnfSpecs.tables5 := by
  have hm := gt_mem n gs n (le_refl n) (by omega)
  obtain ⟨n1, n2, n3⟩ := h.nondegenerate _ hm
  unfold bits
  revert n1 n2 n3
  cases (gt n gs n).op false true <;> cases (gt n gs n).op true false <;>
    cases (gt n gs n).op true true <;> simp [CnfSpecs.tables5]

lemma bits_mem4 (f : List Bool → Bool) (R : Opts) (h : Adm n f R gs ou neg) (hpos : 0 < gs.length)
    (hR : R.table = true) (hS : ∀ u < n, R.S u) : bits n gs n ∈ CnfSpecs.tables4 := by
  have hm := gt_mem n gs n (le_refl n) (by omega)
  obtain ⟨n1, n2, n3⟩ := h.nondegenerate _ hm
  obtain ⟨hab, hbn, -⟩ := nodeV_gate n gs h.shaped n (le_refl n) (by omega) 0
  have hg : gt n gs n = gs[0] := by rw [gt_eq n gs n (by omega)]; simp
  have hT := h.table hR hpos (hS _ (by rw [← hg]; omega)) (hS _ (by rw [← hg]; omega))
  rw [← hg] at hT
  unfold T100 at hT
  unfold bits
  revert n1 n2 n3 hT
  cases (gt n gs n).op false true <;> cases (gt n gs n).op true false <;>
    cases (gt n gs n).op true true <;> simp [CnfSpecs.tables4]

end Cover

theorem cover5 (q : ℕ) (gs : List Gate) (ou : ℕ) (neg : Bool)
    (h : Adm 5 (mod3 q) Mod3Tower.cube5 gs ou neg) (hl : gs.length = 9) :
    ∃ L ∈ CnfSpecs.leaves5, ∀ l ∈ L.cube, ev 5 gs ou neg l.1 = l.2 := by
  apply tree_cover _ _ _ _ _ _ _ (by simp)
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨tableLevel_true 5 gs ou neg _ (bits_mem4 5 gs ou neg _ _ h (by omega) rfl (fun _ h => h)),
    pairLevel_true 5 gs ou neg h.shaped 6 (by omega) (by omega)⟩

theorem coverW2 (gs : List Gate) (ou : ℕ) (neg : Bool) (h : Adm 5 w2 Mod3Tower.w2cube gs ou neg)
    (hpos : 0 < gs.length) :
    ∃ L ∈ CnfSpecs.leavesW2, ∀ l ∈ L.cube, ev 5 gs ou neg l.1 = l.2 := by
  apply tree_cover _ _ _ _ _ _ _ (by simp)
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨pairLevel_true 5 gs ou neg h.shaped 5 (by omega) (by omega),
    tableLevel_true 5 gs ou neg _ (bits_mem5 5 gs ou neg _ _ h hpos)⟩

/-- **The r = 12 cover**: whatever the tree data says, every 12-gate `Adm` circuit lies in a leaf. -/
theorem cover12 (gs : List Gate) (ou : ℕ) (neg : Bool) (h : Adm 6 (mod3 1) Mod3Tower.full6 gs ou neg)
    (hl : gs.length = 12) :
    ∃ L ∈ CnfSpecs.leaves12, ∀ l ∈ L.cube, ev 6 gs ou neg l.1 = l.2 := by
  apply tree_cover _ _ _ _ _ _ _ (by simp)
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨tableLevel_true 6 gs ou neg _ (bits_mem4 6 gs ou neg _ _ h (by omega) rfl (fun _ h => h)),
    pairLevel_true 6 gs ou neg h.shaped 7 (by omega) (by omega),
    pairLevel_true 6 gs ou neg h.shaped 8 (by omega) (by omega),
    pairLevel_true 6 gs ou neg h.shaped 9 (by omega) (by omega),
    pairLevel_true 6 gs ou neg h.shaped 10 (by omega) (by omega)⟩

/-! ### The theorem -/

section Final
open CnfSpecs

/-- The 22 CNF hypotheses give the 22 `NoAdm` hypotheses of `Mod3Tower.mod3_6_lower_sat`. -/
theorem noAdm_all
    (h3_0 : ScanUnsat (best 3 0) 1 2) (h3_1 : ScanUnsat (best 3 1) 1 3) (h3_2 : ScanUnsat (best 3 2) 1 3)
    (h4_0 : ScanUnsat (best 4 0) 1 6) (h4_1 : ScanUnsat (best 4 1) 1 6) (h4_2 : ScanUnsat (best 4 2) 1 5)
    (h5_0 : ScanUnsat (best 5 0) 1 8) (h5_0c : LeavesUnsat (fun _ => cube5 0) 9 leaves5)
    (h5_1 : ScanUnsat (best 5 1) 1 8)
    (h5_2 : ScanUnsat (best 5 2) 1 8) (h5_2c : LeavesUnsat (fun _ => cube5 2) 9 leaves5)
    (hw3_0 : ScanUnsat (restrW 3 0) 1 3) (hw3_1 : ScanUnsat (restrW 3 1) 1 3)
    (hw3_2 : ScanUnsat (restrW 3 2) 1 2) (hw4_0 : ScanUnsat (restrW 4 0) 1 6)
    (hw4_1 : ScanUnsat (restrW 4 1) 1 5) (hpq : ScanUnsat restrPq 1 6)
    (hw_s : ScanUnsat w2best 1 7) (hw_8 : LeavesUnsat (fun _ => w2cube) 8 leavesW2)
    (hw_9 : LeavesUnsat (fun _ => w2cube) 9 leavesW2)
    (h6 : ScanUnsat elim6 1 11) (h12 : LeavesUnsat full6 12 leaves12) :
    (NoAdm 3 (mod3 0) (Mod3Tower.best 3) 1 2 ∧ NoAdm 3 (mod3 1) (Mod3Tower.best 3) 1 3 ∧
      NoAdm 3 (mod3 2) (Mod3Tower.best 3) 1 3) ∧
    (NoAdm 4 (mod3 0) (Mod3Tower.best 4) 1 6 ∧ NoAdm 4 (mod3 1) (Mod3Tower.best 4) 1 6 ∧
      NoAdm 4 (mod3 2) (Mod3Tower.best 4) 1 5) ∧
    (NoAdm 5 (mod3 0) (Mod3Tower.best 5) 1 8 ∧ NoAdm 5 (mod3 0) Mod3Tower.cube5 9 9 ∧
      NoAdm 5 (mod3 1) (Mod3Tower.best 5) 1 8 ∧ NoAdm 5 (mod3 2) (Mod3Tower.best 5) 1 8 ∧
      NoAdm 5 (mod3 2) Mod3Tower.cube5 9 9) ∧
    (NoAdm 3 (wq 0) Mod3Tower.restr 1 3 ∧ NoAdm 3 (wq 1) Mod3Tower.restr 1 3 ∧
      NoAdm 3 (wq 2) Mod3Tower.restr 1 2 ∧ NoAdm 4 (wq 0) Mod3Tower.restr 1 6 ∧
      NoAdm 4 (wq 1) Mod3Tower.restr 1 5 ∧ NoAdm 4 pq Mod3Tower.restr 1 6) ∧
    (NoAdm 5 w2 Mod3Tower.w2best 1 7 ∧ NoAdm 5 w2 Mod3Tower.w2cube 8 8 ∧
      NoAdm 5 w2 Mod3Tower.w2cube 9 9) ∧
    (NoAdm 6 (mod3 1) Mod3Tower.elim6 1 11 ∧ NoAdm 6 (mod3 1) Mod3Tower.full6 12 12) := by
  obtain ⟨t3, t4, t5, t6, tw3, tw4, tpq, tw2⟩ := tt_facts
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact noAdm_scan 3 _ _ _ _ (t3 0 (by omega)) (fits_best 3) 1 2 h3_0
  · exact noAdm_scan 3 _ _ _ _ (t3 1 (by omega)) (fits_best 3) 1 3 h3_1
  · exact noAdm_scan 3 _ _ _ _ (t3 2 (by omega)) (fits_best 3) 1 3 h3_2
  · exact noAdm_scan 4 _ _ _ _ (t4 0 (by omega)) (fits_best 4) 1 6 h4_0
  · exact noAdm_scan 4 _ _ _ _ (t4 1 (by omega)) (fits_best 4) 1 6 h4_1
  · exact noAdm_scan 4 _ _ _ _ (t4 2 (by omega)) (fits_best 4) 1 5 h4_2
  · exact noAdm_scan 5 _ _ _ _ (t5 0 (by omega)) (fits_best 5) 1 8 h5_0
  · exact noAdm_leaves 5 _ _ _ (fun _ => cube5O) (t5 0 (by omega)) (fun _ => fits_cube5) 9 leaves5
      (fun gs ou neg h hl => cover5 0 gs ou neg h hl) h5_0c
  · exact noAdm_scan 5 _ _ _ _ (t5 1 (by omega)) (fits_best 5) 1 8 h5_1
  · exact noAdm_scan 5 _ _ _ _ (t5 2 (by omega)) (fits_best 5) 1 8 h5_2
  · exact noAdm_leaves 5 _ _ _ (fun _ => cube5O) (t5 2 (by omega)) (fun _ => fits_cube5) 9 leaves5
      (fun gs ou neg h hl => cover5 2 gs ou neg h hl) h5_2c
  · exact noAdm_scan 3 _ _ _ _ (tw3 0 (by omega)) (fits_restr 3) 1 3 hw3_0
  · exact noAdm_scan 3 _ _ _ _ (tw3 1 (by omega)) (fits_restr 3) 1 3 hw3_1
  · exact noAdm_scan 3 _ _ _ _ (tw3 2 (by omega)) (fits_restr 3) 1 2 hw3_2
  · exact noAdm_scan 4 _ _ _ _ (tw4 0 (by omega)) (fits_restr 4) 1 6 hw4_0
  · exact noAdm_scan 4 _ _ _ _ (tw4 1 (by omega)) (fits_restr 4) 1 5 hw4_1
  · exact noAdm_scan 4 _ _ _ _ tpq (fits_restr 4) 1 6 hpq
  · exact noAdm_scan 5 _ _ _ _ tw2 fits_w2best 1 7 hw_s
  · exact noAdm_leaves 5 _ _ _ (fun _ => w2cubeO) tw2 (fun _ => fits_w2cube) 8 leavesW2
      (fun gs ou neg h hl => coverW2 gs ou neg h (by omega)) hw_8
  · exact noAdm_leaves 5 _ _ _ (fun _ => w2cubeO) tw2 (fun _ => fits_w2cube) 9 leavesW2
      (fun gs ou neg h hl => coverW2 gs ou neg h (by omega)) hw_9
  · exact noAdm_scan 6 _ _ _ _ t6 fits_elim6 1 11 h6
  · exact noAdm_leaves 6 _ _ _ (fun g => full6O (decide (1 ≤ g)) (decide (2 ≤ g))) t6
      (fun _ => fits_full6 _ _) 12 leaves12 (fun gs ou neg h hl => cover12 gs ou neg h hl) h12

/-- **`size(MOD3^1_6) = size(MOD3^2_6) = 13`.** Every hypothesis says that a CNF generated in Lean
(`CnfGen`; each leaf byte-identical to the one its ledger records as refuted, each scan CNF
re-solved from the export) is unsatisfiable, as a
`Std.Sat.CNF Nat`: the type `lratcheck`'s verified checker proves `Unsat` of. One hypothesis per
run: for scans, its CNF at every `r` it refuted; for split runs, every leaf's CNF. The upper bound
is `Mod3Upper`'s 13-gate circuit. -/
theorem mod3_6_size_13
    (h3_0 : ScanUnsat (best 3 0) 1 2) (h3_1 : ScanUnsat (best 3 1) 1 3) (h3_2 : ScanUnsat (best 3 2) 1 3)
    (h4_0 : ScanUnsat (best 4 0) 1 6) (h4_1 : ScanUnsat (best 4 1) 1 6) (h4_2 : ScanUnsat (best 4 2) 1 5)
    (h5_0 : ScanUnsat (best 5 0) 1 8) (h5_0c : LeavesUnsat (fun _ => cube5 0) 9 leaves5)
    (h5_1 : ScanUnsat (best 5 1) 1 8)
    (h5_2 : ScanUnsat (best 5 2) 1 8) (h5_2c : LeavesUnsat (fun _ => cube5 2) 9 leaves5)
    (hw3_0 : ScanUnsat (restrW 3 0) 1 3) (hw3_1 : ScanUnsat (restrW 3 1) 1 3)
    (hw3_2 : ScanUnsat (restrW 3 2) 1 2) (hw4_0 : ScanUnsat (restrW 4 0) 1 6)
    (hw4_1 : ScanUnsat (restrW 4 1) 1 5) (hpq : ScanUnsat restrPq 1 6)
    (hw_s : ScanUnsat w2best 1 7) (hw_8 : LeavesUnsat (fun _ => w2cube) 8 leavesW2)
    (hw_9 : LeavesUnsat (fun _ => w2cube) 9 leavesW2)
    (h6 : ScanUnsat elim6 1 11) (h12 : LeavesUnsat full6 12 leaves12) :
    (LB 6 (mod3 1) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 1 gs) ∧
      (LB 6 (mod3 2) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 2 gs) := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4, c5⟩, ⟨d1, d2, d3, d4, d5, d6⟩,
    ⟨e1, e2, e3⟩, f1, f2⟩ := noAdm_all h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c
      hw3_0 hw3_1 hw3_2 hw4_0 hw4_1 hpq hw_s hw_8 hw_9 h6 h12
  exact ⟨⟨Mod3Tower.mod3_6_lower_sat a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 c5 d1 d2 d3 d4 d5 d6 e1 e2 e3 f1 f2,
      Mod3Upper.c13, Mod3Upper.c13_length, Mod3Upper.mod3_1_upper⟩,
    ⟨Mod3Tower.mod3_2_6_lower_sat a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 c5 d1 d2 d3 d4 d5 d6 e1 e2 e3 f1 f2,
      Mod3Upper.mod3_2_upper⟩⟩

/-- **Positive control (conditional).** Under the same hypotheses, the full r = 12 encoding
(`…_x_S_E`) at r = 13 is satisfiable, through `Mod3Tower.full6_sat13`: if the hypotheses hold,
what they rule out is 12 gates, not every size. The unconditional counterpart is outside Lean:
`cnf_certify.py` checks that the SAT cube's recorded model satisfies Lean's r = 13 CNF of it. -/
theorem cnf13_sat
    (h3_0 : ScanUnsat (best 3 0) 1 2) (h3_1 : ScanUnsat (best 3 1) 1 3) (h3_2 : ScanUnsat (best 3 2) 1 3)
    (h4_0 : ScanUnsat (best 4 0) 1 6) (h4_1 : ScanUnsat (best 4 1) 1 6) (h4_2 : ScanUnsat (best 4 2) 1 5)
    (h5_0 : ScanUnsat (best 5 0) 1 8) (h5_0c : LeavesUnsat (fun _ => cube5 0) 9 leaves5)
    (h5_1 : ScanUnsat (best 5 1) 1 8)
    (h5_2 : ScanUnsat (best 5 2) 1 8) (h5_2c : LeavesUnsat (fun _ => cube5 2) 9 leaves5)
    (hw3_0 : ScanUnsat (restrW 3 0) 1 3) (hw3_1 : ScanUnsat (restrW 3 1) 1 3)
    (hw3_2 : ScanUnsat (restrW 3 2) 1 2) (hw4_0 : ScanUnsat (restrW 4 0) 1 6)
    (hw4_1 : ScanUnsat (restrW 4 1) 1 5) (hpq : ScanUnsat restrPq 1 6)
    (hw_s : ScanUnsat w2best 1 7) (hw_8 : LeavesUnsat (fun _ => w2cube) 8 leavesW2)
    (hw_9 : LeavesUnsat (fun _ => w2cube) 9 leavesW2)
    (h6 : ScanUnsat elim6 1 11) (h12 : LeavesUnsat full6 12 leaves12) :
    ¬ (toCNF ((full6 2).cnf 13)).Unsat := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4, c5⟩, ⟨d1, d2, d3, d4, d5, d6⟩,
    ⟨e1, e2, e3⟩, f1, f2⟩ := noAdm_all h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c
      hw3_0 hw3_1 hw3_2 hw4_0 hw4_1 hpq hw_s hw_8 hw_9 h6 h12
  have h13 := Mod3Tower.full6_sat13 a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 c5 d1 d2 d3 d4 d5 d6 e1 e2 e3 f1 f2
  unfold NoAdm at h13
  push Not at h13
  obtain ⟨gs, ou, neg, hlo, hhi, hadm⟩ := h13
  have hl : gs.length = 13 := by omega
  have := adm_sat 6 (mod3 1) Mod3Tower.full6 gs ou neg hadm _ tt_facts.2.2.2.1 (full6O true true)
    (fits_full6 _ _) [] (by simp)
  rw [hl] at this
  simpa [Run.cnf, full6] using this

/-- **The same theorem, with its hypotheses read off one list**: `CnfSpecs.scanList` and
`splitList` are what `cnfexport list` prints and `cnf_certify.py` certifies, so a range edited in
one place cannot silently differ from the theorem. -/
theorem mod3_6_size_13_lists
    (hS : ∀ x ∈ scanList, ScanUnsat x.run x.lo x.hi)
    (hL : ∀ x ∈ splitList, LeavesUnsat x.run x.r x.leaves) :
    (LB 6 (mod3 1) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 1 gs) ∧
      (LB 6 (mod3 2) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 2 gs) := by
  simp only [scanList, splitList, List.forall_mem_cons] at hS hL
  obtain ⟨h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, hw3_0, hw3_1, hw3_2, hw4_0, hw4_1,
    hpq, hw_s, h6, -⟩ := hS
  obtain ⟨h5_0c, h5_2c, hw_8, hw_9, h12, -⟩ := hL
  exact mod3_6_size_13 h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c hw3_0 hw3_1 hw3_2
    hw4_0 hw4_1 hpq hw_s hw_8 hw_9 h6 h12

/-- The names `cnfexport` looks runs up by are distinct, so `cnfexport scan <name>` and
`leaves <name>` give the listed run (a duplicated name would make the lookup return the first). -/
theorem names_nodup : (scanList.map (·.name)).Nodup ∧ (splitList.map (·.name)).Nodup := by
  decide

end Final

end CnfRuns
