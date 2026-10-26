import Garden.CnfRuns
/-! Must-fail controls for the CNF-in-Lean theorems. Every `theorem K…` below must FAIL to build.
Not part of the library; run with `lake env lean controls/2026-10-24-cnf-must-fail.lean`. -/
open CnfGen CnfSound CnfRuns CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds Mod3Lower Tower W2SemBounds

namespace Ctl

/-- `valBlock` with ONE literal flipped: the (0,0) clause asserts `val` instead of `¬val`. -/
def valBlockF (n i j k t : Nat) (p q : Bool) : List Ev :=
  let a := litVal n j t p
  let b := litVal n k t q
  if a = .fls ∨ b = .fls then [] else
    let prem := ng (.sel i j k) :: (a.negs ++ b.negs)
    if p = false ∧ q = false then [.cl (prem ++ [pos (.val i t)])]
    else [.cl (prem ++ [ng (.val i t), pos (.fbit i p q)]),
          .cl (prem ++ [pos (.val i t), ng (.fbit i p q)])]

section
variable (n : ℕ) (gs : List Gate) (o : ℕ) (negb : Bool)
-- K1: the satisfaction proof of `valBlock_good`, verbatim, on the flipped block
theorem K1_valBlock_flip_good (hs : Shaped n gs) (hn : Normal gs) (i j k t : ℕ) (hi1 : n ≤ i)
    (hi2 : i < n + gs.length) (p q : Bool) :
    ∀ e ∈ valBlockF n i j k t p q, Good (ev n gs o negb) e := by
  intro e he
  simp only [valBlockF] at he
  by_cases hA : litVal n j t p = .fls ∨ litVal n k t q = .fls
  · rw [if_pos hA] at he; simp at he
  rw [if_neg hA] at he
  -- every clause starts with the premise `¬sel ∨ ¬(x_j = p) ∨ ¬(x_k = q)`
  have prem : ∀ c : List L,
      (ng (.sel i j k) :: ((litVal n j t p).negs ++ (litVal n k t q).negs)).Sublist c →
      (¬ ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∨ nodeV n gs t j ≠ p ∨ nodeV n gs t k ≠ q) →
      Good (ev n gs o negb) (.cl c) := by
    intro c hsub hcase
    rcases hcase with h | h | h
    · exact good_ng (.sel i j k) (hsub.subset (by simp)) (ev_sel_false n gs o negb i j k h)
    · rcases litVal_ne n gs o negb t j p h with h' | ⟨l, hl, hv⟩
      · exact absurd (Or.inl h') hA
      · exact good_cl l (hsub.subset (by simp [hl])) hv
    · rcases litVal_ne n gs o negb t k q h with h' | ⟨l, hl, hv⟩
      · exact absurd (Or.inr h') hA
      · exact good_cl l (hsub.subset (by simp [hl])) hv
  have hg : gt n gs i ∈ gs := by rw [gt_eq n gs i (by omega)]; exact List.getElem_mem _
  obtain ⟨-, -, hv⟩ := nodeV_gate n gs hs i hi1 hi2 t
  by_cases h2 : p = false ∧ q = false
  · rw [if_pos h2] at he
    simp only [List.mem_singleton] at he
    subst he
    by_cases hc : ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∧ nodeV n gs t j = p ∧ nodeV n gs t k = q
    · obtain ⟨⟨ha, hb⟩, hP, hQ⟩ := hc
      refine good_ng (.val i t) (by simp) ?_
      simp only [ev]
      rw [hv, ha, hb, hP, hQ, h2.1, h2.2]; exact hn _ hg
    · exact prem _ (by simp) (by tauto)
  · rw [if_neg h2] at he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    by_cases hc : ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∧ nodeV n gs t j = p ∧ nodeV n gs t k = q
    · obtain ⟨⟨ha, hb⟩, hP, hQ⟩ := hc
      have hv' : nodeV n gs t i = (gt n gs i).op p q := by rw [hv, ha, hb, hP, hQ]
      rcases he with rfl | rfl
      · cases hx : nodeV n gs t i
        · exact good_ng (.val i t) (by simp) (by simp [ev, hx])
        · exact good_pos (.fbit i p q) (by simp) (by simp [ev, ← hv', hx])
      · cases hx : nodeV n gs t i
        · exact good_ng (.fbit i p q) (by simp) (by simp [ev, ← hv', hx])
        · exact good_pos (.val i t) (by simp) (by simp [ev, hx])
    · rcases he with rfl | rfl
      · exact prem _ (by simp) (by tauto)
      · exact prem _ (by simp) (by tauto)


end

-- K2: the numbering lemma without its hypothesis (every event `Good`)
theorem K2_number_no_good (ev : M → Bool) (evs : List Ev) :
    (toCNF (cnfOf evs)).eval (assign ev evs) = true :=
  number_sat ev evs (fun e _ => by trivial)

-- K3: options asking for a family the run does not grant (`elim` against `best 6`)
theorem K3_fits_elim_best : Fits 6 (Mod3Tower.best 6) CnfSpecs.elim6O where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := fun s h => by
    cases h; exact ⟨fun c => Mod3SemBounds.c5 ((4 - c.toNat) % 3), rfl, by decide, by decide⟩
  elim2 := fun _ h => by cases h
  red := fun _ h => by cases h
  symin := fun h => by cases h
  symvars := fun _ h => by cases h
  table := fun h => by cases h

-- K4: the r = 12 options against the r ≤ 11 run's `Opts` (no `sem` clauses there)
theorem K4_fits_full6_elim6 : Fits 6 Mod3Tower.elim6 (CnfSpecs.full6O true true) where
  first01 := fun _ => rfl
  allin := fun _ => rfl
  elim := (fits_full6 true true).elim
  elim2 := (fits_full6 true true).elim2
  red := (fits_full6 true true).red
  symin := (fits_full6 true true).symin
  symvars := fun _ h => by cases h
  table := (fits_full6 true true).table

-- K5: a leaf's CNF as base ++ cube numbered WITHOUT resetting `out` (would repeat the base)
theorem K5_leafCnf_no_reset (R : CnfSpecs.Run) (r : ℕ) (cube : List L) :
    R.leafCnf r cube = R.cnf r ++
      ((cube.map fun l => Ev.cl [l]).foldl NS.step (number (events R.n r R.tt R.o))).out.toList := by
  rw [leafCnf_split]

-- K6: the DIMACS header counting only the base's clauses
theorem K6_dimacs_count (A B : List (List ℤ)) :
    dimacs (A ++ B) = header (max (maxVar A) (maxVar B)) A.length ++ body A ++ body B := by
  rw [dimacs_append]

-- K7: the n = 6 truth table against the wrong residue
theorem K7_tt_wrong : ∀ t < 2 ^ 6, CnfSpecs.mod3T 1 6 t = mod3 2 (row 6 t) := by decide +kernel

-- K8: the tree cover without the per-level facts
theorem K8_tree_no_levels (P : L → Prop) (tagF : ℕ → ℕ → Option ℕ) (dflt : ℕ)
    (levels : List (List (List L))) (d p : ℕ) (c : List L) (hc : ∀ l ∈ c, P l) :
    ∃ Lf ∈ CnfSpecs.tree tagF dflt d levels p c, ∀ l ∈ Lf.cube, P l :=
  tree_cover P tagF dflt levels d p c hc (fun lv _ => by simp)

-- K9: the first gate's table among only three of the four table cubes
theorem K9_bits_three (gs : List Gate) (ou : ℕ) (neg : Bool)
    (h : Adm 6 (mod3 1) Mod3Tower.full6 gs ou neg) (hpos : 0 < gs.length) :
    bits 6 gs 6 ∈ [(false, false, true), (false, true, false), (true, true, false)] := by
  have hm := gt_mem 6 gs 6 (le_refl 6) (by omega)
  obtain ⟨n1, n2, n3⟩ := h.nondegenerate _ hm
  obtain ⟨hab, hbn, -⟩ := nodeV_gate 6 gs h.shaped 6 (le_refl 6) (by omega) 0
  have hg : gt 6 gs 6 = gs[0] := by rw [gt_eq 6 gs 6 (by omega)]; simp
  have hT := h.table rfl hpos (by rw [← hg]; show _ < 6; omega) (by rw [← hg]; show _ < 6; omega)
  rw [← hg] at hT
  unfold T100 at hT
  unfold bits
  revert n1 n2 n3 hT
  cases (gt 6 gs 6).op false true <;> cases (gt 6 gs 6).op true false <;>
    cases (gt 6 gs 6).op true true <;> simp

-- K10: the r = 12 run with the hypothesis for its first leaf (index 0) left out
theorem K10_drop_leaf (h12 : ∀ L ∈ CnfSpecs.leaves12, L.idx ≠ 0 →
      (toCNF ((CnfSpecs.full6 L.tag).leafCnf 12 L.cube)).Unsat) :
    NoAdm 6 (mod3 1) Mod3Tower.full6 12 12 :=
  noAdm_leaves 6 _ _ _ (fun g => CnfSpecs.full6O (decide (1 ≤ g)) (decide (2 ≤ g))) tt_facts.2.2.2.1
    (fun _ => fits_full6 _ _) 12 CnfSpecs.leaves12
    (fun gs ou neg h hl => cover12 gs ou neg h hl) h12

-- K11: a scan's range one short (r ≤ 7 for MOD3_5^0) claimed to give r ≤ 8
theorem K11_scan_short (h : ScanUnsat (CnfSpecs.best 5 0) 1 7) : NoAdm 5 (mod3 0) (Mod3Tower.best 5) 1 8 :=
  noAdm_scan 5 _ _ _ _ (tt_facts.2.2.1 0 (by omega)) (fits_best 5) 1 8 h

-- K12: the final theorem claiming 14
theorem K12_claim14
    (h3_0 : ScanUnsat (CnfSpecs.best 3 0) 1 2) (h3_1 : ScanUnsat (CnfSpecs.best 3 1) 1 3)
    (h3_2 : ScanUnsat (CnfSpecs.best 3 2) 1 3) (h4_0 : ScanUnsat (CnfSpecs.best 4 0) 1 6)
    (h4_1 : ScanUnsat (CnfSpecs.best 4 1) 1 6) (h4_2 : ScanUnsat (CnfSpecs.best 4 2) 1 5)
    (h5_0 : ScanUnsat (CnfSpecs.best 5 0) 1 8)
    (h5_0c : LeavesUnsat (fun _ => CnfSpecs.cube5 0) 9 CnfSpecs.leaves5)
    (h5_1 : ScanUnsat (CnfSpecs.best 5 1) 1 8) (h5_2 : ScanUnsat (CnfSpecs.best 5 2) 1 8)
    (h5_2c : LeavesUnsat (fun _ => CnfSpecs.cube5 2) 9 CnfSpecs.leaves5)
    (hw3_0 : ScanUnsat (CnfSpecs.restrW 3 0) 1 3) (hw3_1 : ScanUnsat (CnfSpecs.restrW 3 1) 1 3)
    (hw3_2 : ScanUnsat (CnfSpecs.restrW 3 2) 1 2) (hw4_0 : ScanUnsat (CnfSpecs.restrW 4 0) 1 6)
    (hw4_1 : ScanUnsat (CnfSpecs.restrW 4 1) 1 5) (hpq : ScanUnsat CnfSpecs.restrPq 1 6)
    (hw_s : ScanUnsat CnfSpecs.w2best 1 7)
    (hw_8 : LeavesUnsat (fun _ => CnfSpecs.w2cube) 8 CnfSpecs.leavesW2)
    (hw_9 : LeavesUnsat (fun _ => CnfSpecs.w2cube) 9 CnfSpecs.leavesW2)
    (h6 : ScanUnsat CnfSpecs.elim6 1 11) (h12 : LeavesUnsat CnfSpecs.full6 12 CnfSpecs.leaves12) :
    LB 6 (mod3 1) 14 :=
  (mod3_6_size_13 h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c hw3_0 hw3_1 hw3_2 hw4_0
    hw4_1 hpq hw_s hw_8 hw_9 h6 h12).1.1

-- K13: the positive control at r = 12 (it would contradict `h12`)
theorem K13_sat12
    (h3_0 : ScanUnsat (CnfSpecs.best 3 0) 1 2) (h3_1 : ScanUnsat (CnfSpecs.best 3 1) 1 3)
    (h3_2 : ScanUnsat (CnfSpecs.best 3 2) 1 3) (h4_0 : ScanUnsat (CnfSpecs.best 4 0) 1 6)
    (h4_1 : ScanUnsat (CnfSpecs.best 4 1) 1 6) (h4_2 : ScanUnsat (CnfSpecs.best 4 2) 1 5)
    (h5_0 : ScanUnsat (CnfSpecs.best 5 0) 1 8)
    (h5_0c : LeavesUnsat (fun _ => CnfSpecs.cube5 0) 9 CnfSpecs.leaves5)
    (h5_1 : ScanUnsat (CnfSpecs.best 5 1) 1 8) (h5_2 : ScanUnsat (CnfSpecs.best 5 2) 1 8)
    (h5_2c : LeavesUnsat (fun _ => CnfSpecs.cube5 2) 9 CnfSpecs.leaves5)
    (hw3_0 : ScanUnsat (CnfSpecs.restrW 3 0) 1 3) (hw3_1 : ScanUnsat (CnfSpecs.restrW 3 1) 1 3)
    (hw3_2 : ScanUnsat (CnfSpecs.restrW 3 2) 1 2) (hw4_0 : ScanUnsat (CnfSpecs.restrW 4 0) 1 6)
    (hw4_1 : ScanUnsat (CnfSpecs.restrW 4 1) 1 5) (hpq : ScanUnsat CnfSpecs.restrPq 1 6)
    (hw_s : ScanUnsat CnfSpecs.w2best 1 7)
    (hw_8 : LeavesUnsat (fun _ => CnfSpecs.w2cube) 8 CnfSpecs.leavesW2)
    (hw_9 : LeavesUnsat (fun _ => CnfSpecs.w2cube) 9 CnfSpecs.leavesW2)
    (h6 : ScanUnsat CnfSpecs.elim6 1 11) (h12 : LeavesUnsat CnfSpecs.full6 12 CnfSpecs.leaves12) :
    ¬ (toCNF ((CnfSpecs.full6 2).cnf 12)).Unsat := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4, c5⟩, ⟨d1, d2, d3, d4, d5, d6⟩,
    ⟨e1, e2, e3⟩, f1, f2⟩ := noAdm_all h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c
      hw3_0 hw3_1 hw3_2 hw4_0 hw4_1 hpq hw_s hw_8 hw_9 h6 h12
  have h13 := Mod3Tower.full6_sat13 a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 c5 d1 d2 d3 d4 d5 d6 e1 e2 e3 f1 f2
  unfold NoAdm at h13
  push Not at h13
  obtain ⟨gs, ou, neg, hlo, hhi, hadm⟩ := h13
  have hl : gs.length = 12 := by omega
  have := adm_sat 6 (mod3 1) Mod3Tower.full6 gs ou neg hadm _ tt_facts.2.2.2.1 (CnfSpecs.full6O true true)
    (fits_full6 _ _) [] (by simp)
  rw [hl] at this
  simpa [CnfSpecs.Run.cnf, CnfSpecs.full6] using this

-- K14: the list form with the first scan (MOD3_3^0) left out of its hypothesis
theorem K14_lists_short (hS : ∀ x ∈ CnfSpecs.scanList.tail, ScanUnsat x.run x.lo x.hi)
    (hL : ∀ x ∈ CnfSpecs.splitList, LeavesUnsat x.run x.r x.leaves) :
    (LB 6 (mod3 1) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 1 gs) ∧
      (LB 6 (mod3 2) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 2 gs) :=
  mod3_6_size_13_lists hS hL

-- K15: name uniqueness for a list with a scan name repeated (as a mistyped entry would)
theorem K15_names_dup : ("best4_0" :: CnfSpecs.scanList.map (·.name)).Nodup := by decide

end Ctl
