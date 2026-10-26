import Std.Tactic.BVDecide.LRAT.Checker

/-!
# Streaming Lean's verified LRAT checker (research session 2026-09-28)

Lean core ships an LRAT checker with a soundness proof:
`Std.Tactic.BVDecide.LRAT.check_sound : check proof cnf → cnf.Unsat`.
It takes the whole proof as one `Array IntAction`, so a proof of 10+ GB cannot be held in 8 GB.

This file runs the *same* step function one chunk at a time, carrying the formula between
chunks, and proves that this changes nothing:

* `runChunks_eq`: running the chunks `cs` in sequence gives exactly the result of core's
  `compactLratChecker.go` on their concatenation.
* `runChunks_sound`: hence if `runChunks (CNF.convertLRAT cnf) cs = .success`, then `cnf`
  is unsatisfiable (`Std.Sat.CNF.Unsat`: every assignment falsifies some clause).

What is assumed, in plain words. The theorem is about whatever `cnf` and `cs` the executable
builds. That the `cnf` is the DIMACS file on disk, and that the executable's IO loop feeds
chunks in the shape of `runChunks`, is glue and is not verified (see `LratCheck.lean`). Which
actions the parser produces is irrelevant to soundness: any action list that is accepted
proves `cnf.Unsat`. That the CNF says "no circuit of r gates" is the encoding's correctness,
argued and tested in `research/circuits/`, not here.
-/

open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal

namespace Garden.LratStream

/-- `compactLratChecker.go` with one change: running off the end of the array returns the
current formula (`.inr f`) instead of `.outOfProof`, so the next chunk can continue from it. -/
def stepChunk {n : Nat} (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat) :
    Sum Result (DefaultFormula n) :=
  if h : idx < proof.size then
    let step := intActionToDefaultClauseAction n proof[idx]
    match step with
    | none => stepChunk f proof (idx + 1)
    | some (.addEmpty _ rupHints) =>
      let (_, checkSuccess) := Formula.performRupAdd f Clause.empty rupHints
      if checkSuccess then .inl .success else .inl .rupFailure
    | some (.addRup _ c rupHints) =>
      let (f, checkSuccess) := Formula.performRupAdd f c rupHints
      if checkSuccess then stepChunk f proof (idx + 1) else .inl .rupFailure
    | some (.addRat _ c pivot rupHints ratHints) =>
      if pivot ∈ Clause.toList c then
        let (f, checkSuccess) := Formula.performRatAdd f c pivot rupHints ratHints
        if checkSuccess then stepChunk f proof (idx + 1) else .inl .rupFailure
      else
        stepChunk f proof (idx + 1)
    | some (.del ids) => stepChunk (Formula.delete f ids) proof (idx + 1)
  else
    .inr f
termination_by proof.size - idx

/-- Run the chunks in order, carrying the formula; end of input without the empty clause is
`.outOfProof`, as in core. -/
def runChunks {n : Nat} (f : DefaultFormula n) : List (Array IntAction) → Result
  | [] => .outOfProof
  | c :: cs =>
    match stepChunk f c 0 with
    | .inl r => r
    | .inr f' => runChunks f' cs

/-- Starting past a prefix `p` in `p ++ q` is starting at the same place in `q`. -/
theorem go_append_shift {n : Nat} (f : DefaultFormula n) (p q : Array IntAction) (j : Nat) :
    compactLratChecker.go f (p ++ q) (p.size + j) = compactLratChecker.go f q j := by
  induction h : q.size - j using Nat.strongRecOn generalizing f j with
  | _ k ih =>
  rw [compactLratChecker.go]; conv => rhs; rw [compactLratChecker.go]
  by_cases hj : j < q.size
  · have hlt : p.size + j < (p ++ q).size := by simp; omega
    have IH : ∀ g, compactLratChecker.go g (p ++ q) (p.size + j + 1)
        = compactLratChecker.go g q (j + 1) := fun g => by
      have := ih (q.size - (j + 1)) (by omega) g (j + 1) rfl
      simpa [Nat.add_assoc] using this
    simp only [hlt, hj, dite_true, Array.getElem_append_right (by omega : p.size ≤ p.size + j),
      Nat.add_sub_cancel_left]
    cases intActionToDefaultClauseAction n q[j] with
    | none => simp [IH]
    | some a => cases a <;> simp [IH]
  · have hlt : ¬ p.size + j < (p ++ q).size := by simp; omega
    simp [hj]

/-- Continue with `go` over `q` if the chunk ran out without a verdict. -/
def thenGo {n : Nat} : Sum Result (DefaultFormula n) → Array IntAction → Result
  | .inl r, _ => r
  | .inr f', q => compactLratChecker.go f' q 0

/-- One chunk: `go` over `p ++ q` from `i` is `stepChunk` over `p`, then `go` over `q`. -/
theorem go_append_stepChunk {n : Nat} (f : DefaultFormula n) (p q : Array IntAction) (i : Nat)
    (hi : i ≤ p.size) :
    compactLratChecker.go f (p ++ q) i =
      thenGo (stepChunk f p i) q := by
  induction h : p.size - i using Nat.strongRecOn generalizing f i with
  | _ k ih =>
  by_cases hj : i < p.size
  · have hlt : i < (p ++ q).size := by simp; omega
    have IH : ∀ g, compactLratChecker.go g (p ++ q) (i + 1) =
        thenGo (stepChunk g p (i + 1)) q :=
      fun g => ih (p.size - (i + 1)) (by omega) g (i + 1) (by omega) rfl
    rw [compactLratChecker.go, stepChunk]
    simp only [hlt, hj, dite_true, Array.getElem_append_left hj]
    cases intActionToDefaultClauseAction n p[i] with
    | none => simp [IH]
    | some a =>
      cases a with
      | addEmpty => simp; split <;> simp_all [thenGo]
      | addRup _ c hs => simp; split <;> simp_all [thenGo]
      | addRat _ c piv hs rs => simp; split <;> (try split) <;> simp_all [thenGo]
      | del => simp [IH]
  · have hi' : i = p.size := by omega
    subst hi'
    rw [stepChunk]
    simp only [Nat.lt_irrefl, dite_false]
    simpa [thenGo] using go_append_shift f p q 0

theorem runChunks_eq {n : Nat} (f : DefaultFormula n) (cs : List (Array IntAction)) :
    runChunks f cs = compactLratChecker.go f (cs.foldr (· ++ ·) #[]) 0 := by
  induction cs generalizing f with
  | nil => simp [runChunks, compactLratChecker.go]
  | cons c cs ih =>
    rw [List.foldr_cons, go_append_stepChunk f c _ 0 (Nat.zero_le _), runChunks]
    split <;> simp_all [thenGo]

/-- **The result.** If the streamed checker accepts, the CNF is unsatisfiable. -/
theorem runChunks_sound (cnf : CNF Nat) (cs : List (Array IntAction)) :
    runChunks (CNF.convertLRAT cnf) cs = .success → cnf.Unsat := by
  intro h
  apply check_sound (cs.foldr (· ++ ·) #[]) cnf
  have h2 : compactLratChecker (CNF.convertLRAT cnf) (cs.foldr (· ++ ·) #[]) = .success := by
    rw [compactLratChecker, ← runChunks_eq]; exact h
  simp [check, h2]

end Garden.LratStream
