import Garden.DirectRuns
/-! Must-fail controls for `Garden/LratDirect.lean` and `Garden/DirectRuns.lean`: one per new
theorem. Every `theorem D…` below must FAIL to build, each with the original proof (verbatim, or
adapted only to the mutated statement's shape). Not part of the library; run with
`lake env lean controls/2026-10-25-direct-must-fail.lean`. Witnesses that the mutated claims of
D1, D6, D11 and D15 are false: `controls/2026-10-25-direct-witness.lean` (builds). D12's needs, besides
the satisfiable `toCNF []` there, a job some bytes verify, which the run shows but Lean does not. The
other controls show that a reused proof no longer fits a mutated claim, which is weaker. -/
set_option autoImplicit false
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal
open Std.Tactic.BVDecide.LRAT (IntAction)
open Garden.LratStream Garden.LratDirect CnfGen CnfSpecs CnfRuns CircuitDual Mod3SemBounds DirectRuns

namespace Ctl

-- D1 `scan_cnf?` without `r ≤ x.hi` (false: `best3_0` at r = 3 is outside its range)
theorem D1_scan_cnf_no_hi {name : String} {x : ScanSpec} {r : Nat} (h : scanSpec? name = some x)
    (hlo : x.lo ≤ r) : (Job.scan name r).cnf? = some (x.run.cnf r) := by
  simp [Job.cnf?, h, hlo]

-- D2 `leaf_cnf?` with the leaf looked up at `i + 1` but the job at `i`
theorem D2_leaf_cnf_shift {name : String} {x : SplitSpec} {i : Nat} {L : Leaf}
    (h : splitSpec? name = some x) (hL : x.leaves[i + 1]? = some L) :
    (Job.leaf name i).cnf? = some ((x.run L.tag).leafCnf x.r L.cube) := by
  simp [Job.cnf?, h, hL]

-- D3 `scanSpec?_mem` claiming the entry is never the first
theorem D3_scanSpec_mem_tail {name : String} {x : ScanSpec} (h : scanSpec? name = some x) :
    x ∈ scanList.tail :=
  List.mem_of_find?_eq_some h

-- D4 `splitSpec?_mem` claiming the entry is never the first
theorem D4_splitSpec_mem_tail {name : String} {x : SplitSpec} (h : splitSpec? name = some x) :
    x ∈ splitList.tail :=
  List.mem_of_find?_eq_some h

-- D5 `foldl_advance_inl` from a formula instead of a verdict (a formula does change)
theorem D5_foldl_advance_inr {n : Nat} (f : DefaultFormula n) (cs : List (Array IntAction)) :
    cs.foldl advance (.inr f : FS n) = .inr f := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [List.foldl, advance] using ih

-- D6 `runChunks_of_advance` from a fold that ended with no verdict (false: `D6_false` in the
-- witness file, at `cs = []`, where `runChunks` is `.outOfProof`)
theorem D6_runChunks_no_verdict {n : Nat} (f f' : DefaultFormula n) (cs : List (Array IntAction))
    (h : cs.foldl advance (.inr f) = .inr f') : runChunks f cs = .success := by
  induction cs generalizing f with
  | nil => simp at h
  | cons c cs ih =>
    simp only [List.foldl, advance] at h
    rw [runChunks]
    cases hs : stepChunk f c 0 with
    | inl r => rw [hs, foldl_advance_inl] at h; simpa using h
    | inr f' => rw [hs] at h; exact ih f' h

-- D7 `feed_fs` claiming a block never advances the formula (no chunk)
theorem D7_feed_no_chunk {n : Nat} (st : St n) (b : ByteArray) :
    ∃ cs : List (Array IntAction), cs.length = 0 ∧ (feed st b).fs = cs.foldl advance st.fs := by
  unfold feed
  split
  · exact ⟨[], rfl, rfl⟩
  · exact ⟨[(st.ps.parse b).2], rfl, rfl⟩

-- D8 `finish_fs` claiming the end of the proof never advances the formula
theorem D8_finish_no_chunk {n : Nat} (st : St n) :
    ∃ cs : List (Array IntAction), cs.length = 0 ∧ (finish st).fs = cs.foldl advance st.fs := by
  unfold finish
  split
  · exact ⟨[], rfl, rfl⟩
  · exact ⟨[st.ps.close.2], rfl, rfl⟩

-- D9 `foldl_feed_fs` claiming the blocks leave the formula as it was
theorem D9_foldl_feed_same {n : Nat} (st : St n) (bs : List ByteArray) :
    (bs.foldl feed st).fs = st.fs := by
  induction bs generalizing st with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨cs₁, h₁⟩ := feed_fs st b
    rw [List.foldl_cons, ih (feed st b), h₁]

-- D10 `run_fs` with the history starting from a verdict instead of the CNF
theorem D10_run_fs_inl (cnf : CNF Nat) (bs : List ByteArray) :
    ∃ cs : List (Array IntAction), (run cnf bs).fs = cs.foldl advance (.inl .rupFailure) := by
  obtain ⟨cs₁, h₁⟩ := foldl_feed_fs (init cnf) bs
  obtain ⟨cs₂, h₂⟩ := finish_fs (bs.foldl feed (init cnf))
  exact ⟨cs₁ ++ cs₂, by rw [Garden.LratDirect.run, h₂, h₁, List.foldl_append]; rfl⟩

-- D11 `check_sound` for a checker that also accepts a proof ending without the empty clause
def verifiedBad (o : Outcome) : Bool := o.err.isNone && (o.result == .success || o.result == .outOfProof)

theorem D11_check_sound_outOfProof (cnf : CNF Nat) (bs : List ByteArray)
    (h : verifiedBad (check cnf bs) = true) : cnf.Unsat := by
  obtain ⟨cs, hcs⟩ := run_fs cnf bs
  apply runChunks_sound cnf cs
  apply runChunks_of_advance
  rw [← hcs]
  simp only [check, St.outcome, verifiedBad, Bool.and_eq_true, beq_iff_eq] at h
  revert h
  cases (run cnf bs).fs <;> simp

-- D12 `checkJob_sound` without `j.cnf? = some F` (any F would be unsatisfiable)
theorem D12_checkJob_sound_anyF {j : Job} {F : List (List Int)} (bs : List ByteArray)
    (h : (checkJob j bs).verified = true) : (toCNF F).Unsat := by
  simp only [checkJob] at h
  exact check_sound _ bs h

-- D13 `scan_sound` concluding about the next `r` (false, by the run: `best3_0` has a verified
-- proof at r = 2, its top, and its CNF at r = 3 is satisfiable since MOD3_3^0 has a 3-gate circuit;
-- that satisfiability is not proved in Lean, so this control shows only that the proof does not fit)
theorem D13_scan_sound_next {name : String} {x : ScanSpec} {r : Nat} (hx : scanSpec? name = some x)
    (hlo : x.lo ≤ r) (hhi : r ≤ x.hi) (bs : List ByteArray)
    (h : (checkJob (.scan name r) bs).verified = true) : (toCNF (x.run.cnf (r + 1))).Unsat :=
  checkJob_sound (scan_cnf? hx hlo hhi) bs h

-- D14 `leaf_sound` with the job at `i` and the leaf at `i + 1`
theorem D14_leaf_sound_shift {name : String} {x : SplitSpec} {i : Nat} {L : Leaf}
    (hx : splitSpec? name = some x) (hL : x.leaves[i + 1]? = some L) (bs : List ByteArray)
    (h : (checkJob (.leaf name i) bs).verified = true) :
    (toCNF ((x.run L.tag).leafCnf x.r L.cube)).Unsat :=
  checkJob_sound (leaf_cnf? hx hL) bs h

-- D15 `find?_name` without distinct names (false: two entries with one name)
theorem D15_find_name_dup {α : Type} (nm : α → String) (l : List α) {x : α}
    (hx : x ∈ l) : l.find? (fun y => nm y == nm x) = some x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · rw [ih hx']
      split <;> simp_all

-- D16 `scanSpec?_of_mem` for a list with a second `best3_0` (a different run under that name)
theorem D16_scanSpec_dup {x : ScanSpec} (hx : x ∈ scanList ++ [(⟨"best3_0", best 3 1, 1, 2⟩ : ScanSpec)]) :
    (scanList ++ [(⟨"best3_0", best 3 1, 1, 2⟩ : ScanSpec)]).find? (·.name == x.name) = some x :=
  find?_name (fun y : ScanSpec => y.name) scanList names_nodup.1 hx

-- D17 `splitSpec?_of_mem` for a list with a second `cube5_0`
theorem D17_splitSpec_dup {x : SplitSpec}
    (hx : x ∈ splitList ++ [(⟨"cube5_0", fun _ => cube5 2, 9, leaves5⟩ : SplitSpec)]) :
    (splitList ++ [(⟨"cube5_0", fun _ => cube5 2, 9, leaves5⟩ : SplitSpec)]).find? (·.name == x.name) = some x :=
  find?_name (fun y : SplitSpec => y.name) splitList names_nodup.2 hx

-- D18 `scanUnsat_direct` with the checks only below the top of the range
theorem D18_scanUnsat_short {x : ScanSpec} (hx : x ∈ scanList)
    (h : ∀ r, x.lo ≤ r → r < x.hi → ∃ bs, (checkJob (.scan x.name r) bs).verified = true) :
    ScanUnsat x.run x.lo x.hi := by
  intro r hlo hhi
  obtain ⟨bs, hc⟩ := h r hlo hhi
  exact scan_sound (scanSpec?_of_mem hx) hlo hhi bs hc

-- D19 `leavesUnsat_direct` with the last leaf's check missing
theorem D19_leavesUnsat_short {x : SplitSpec} (hx : x ∈ splitList)
    (h : ∀ i, i + 1 < x.leaves.length → ∃ bs, (checkJob (.leaf x.name i) bs).verified = true) :
    LeavesUnsat x.run x.r x.leaves := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨bs, hc⟩ := h i hi
  exact leaf_sound (splitSpec?_of_mem hx) (List.getElem?_eq_getElem hi) bs hc

-- D20 `mod3_6_size_13_direct` claiming 14
theorem D20_direct_14
    (hS : ∀ x ∈ scanList, ∀ r, x.lo ≤ r → r ≤ x.hi →
      ∃ bs, (checkJob (.scan x.name r) bs).verified = true)
    (hL : ∀ x ∈ splitList, ∀ i < x.leaves.length,
      ∃ bs, (checkJob (.leaf x.name i) bs).verified = true) :
    LB 6 (mod3 1) 14 :=
  (mod3_6_size_13_direct hS hL).1.1

end Ctl
