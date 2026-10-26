import Garden.DirectRuns
/-! Witnesses for `controls/2026-10-25-direct-must-fail.lean` (this file builds): the mutated
claims of D1, D6, D11 and D15 are false, so those controls fail because the claim is wrong, not
only because a reused proof no longer fits. For D12, `D12_false` gives the satisfiable CNF; the
other half, a job that some bytes verify, is shown by the run, not in Lean. Run with
`lake env lean controls/2026-10-25-direct-witness.lean`. -/
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal
open Std.Tactic.BVDecide.LRAT (IntAction)
open Garden.LratStream Garden.LratDirect CnfGen CnfSpecs

namespace Wit

/-- The control D11's checker (same definition as `Ctl.verifiedBad` there): it also accepts a
proof that ends without the empty clause. -/
def verifiedBad (o : Outcome) : Bool := o.err.isNone && (o.result == .success || o.result == .outOfProof)

/-- The empty CNF (no clauses) is satisfiable. -/
theorem empty_sat : ¬ (⟨#[]⟩ : CNF Nat).Unsat := by
  intro h
  have := h (fun _ => false)
  simp [CNF.eval] at this

theorem stepChunk_empty {n : Nat} (f : DefaultFormula n) : stepChunk f #[] 0 = .inr f := by
  rw [stepChunk]; simp

/-- With no proof bytes, the checker ends with `.outOfProof` and no parse error. -/
theorem check_empty : (check (⟨#[]⟩ : CNF Nat) []).result = .outOfProof ∧
    (check (⟨#[]⟩ : CNF Nat) []).err = none := by
  simp [check, run, finish, St.stopped, init, PS.close, St.outcome, advance, stepChunk_empty]

/-- D11's claim is false: a checker accepting `.outOfProof` would call the empty CNF unsatisfiable. -/
theorem D11_false :
    ¬ ∀ (cnf : CNF Nat) (bs : List ByteArray), verifiedBad (check cnf bs) = true → cnf.Unsat := by
  intro H
  apply empty_sat
  apply H _ []
  simp [verifiedBad, check_empty.1, check_empty.2]

/-- D6's claim is false: with no chunks the fold ends with the formula, and `runChunks` says
`.outOfProof`. -/
theorem D6_false : ¬ ∀ (n : Nat) (f f' : DefaultFormula n) (cs : List (Array IntAction)),
    cs.foldl advance (.inr f) = .inr f' → runChunks f cs = .success := by
  intro H
  have := H _ (CNF.convertLRAT (⟨#[]⟩ : CNF Nat)) _ [] rfl
  simp [runChunks] at this

/-- D12's claim is false: it would make every `toCNF F` unsatisfiable, but `toCNF []` is the
empty CNF, which is satisfiable. -/
theorem D12_false : ¬ (toCNF [] : CNF Nat).Unsat := empty_sat

/-- D1's claim is false: `best3_0` covers r = 1, 2, so r = 3 names no CNF. -/
theorem D1_false : (Job.scan "best3_0" 3).cnf? = none := by decide

/-- D15's claim is false: in `[a, b]` with one name, looking `b` up finds `a`. -/
theorem D15_false : ([("n", 0), ("n", 1)].find? fun y => y.1 == ("n", 1).1) ≠ some ("n", 1) := by
  decide

end Wit
