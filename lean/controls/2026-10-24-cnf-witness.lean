import Garden.CnfRuns
/-! Supporting checks that must BUILD (controls' witnesses). -/
open CnfGen CnfSound CircuitDual GateElim

/-- The flipped (0,0) clause of `K1` is false for a real normal circuit: one AND gate on two inputs,
row 0. So no proof can show the flipped encoding is satisfied by every circuit. -/
theorem flip_refuted :
    ¬ Good (ev 2 [⟨0, 1, fun a b => a && b⟩] 2 false) (.cl [ng (.sel 2 0 1), pos (.val 2 0)]) := by
  show ¬ ∃ l ∈ [ng (.sel 2 0 1), pos (.val 2 0)], _
  decide

/-- The original clause holds there. -/
theorem orig_holds :
    Good (ev 2 [⟨0, 1, fun a b => a && b⟩] 2 false) (.cl [ng (.sel 2 0 1), ng (.val 2 0)]) := by
  show ∃ l ∈ [ng (.sel 2 0 1), ng (.val 2 0)], _
  decide

/-! The claims of must-fail controls K3 and K4 are not just unprovable by the reused proof: they are
false, and these build. So is K12's conclusion (its implication is false only because the 22
hypotheses hold, which is shown outside Lean). -/

open Tower Mod3SemBounds CnfRuns in
/-- K3's claim is false: `best 6` grants no `elim` bounds for `elim6O`'s to fit. -/
theorem K3_false : ¬ CnfSound.Fits 6 (Mod3Tower.best 6) CnfSpecs.elim6O := by
  intro h
  obtain ⟨e, he, -⟩ := h.elim _ rfl
  simp [Mod3Tower.best] at he

open Tower in
/-- K4's claim is false: the r ≤ 11 run's `Opts` has no `symin`. -/
theorem K4_false : ¬ CnfSound.Fits 6 Mod3Tower.elim6 (CnfSpecs.full6O true true) := by
  intro h
  have := (h.symin rfl).1
  simp [Mod3Tower.elim6, Mod3Tower.best] at this

open Mod3SemBounds in
/-- K12's conclusion is false: `Mod3Upper`'s 13-gate circuit computes `MOD3^1_6`. -/
theorem K12_false : ¬ LB 6 (mod3 1) 14 := by
  intro h
  have hc := (Mod3Tower.computes_iff 1 Mod3Upper.c13).mp Mod3Upper.mod3_1_upper
  have := h Mod3Upper.c13 hc.1 hc.2
  rw [Mod3Upper.c13_length] at this
  omega
