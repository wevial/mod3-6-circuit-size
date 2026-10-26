import Garden.CnfRuns
import Garden.LratDirect

/-!
# size(MOD3^1_6) = size(MOD3^2_6) = 13, from `lratdirect`'s checking function

`CnfRuns.mod3_6_size_13_lists` takes as hypotheses that the Lean-generated CNFs of the 22 runs
are unsatisfiable. `LratDirect.scan_sound` and `leaf_sound` give that from the checking function
`LratDirect.checkJob` accepting some proof bytes for the job. So:

* **`mod3_6_size_13_direct`**: if for every scan in `scanList` and every `r` in its range, and
  for every leaf index of every run in `splitList`, *some* byte blocks make `checkJob` verified,
  then both functions have size exactly 13.

Its hypotheses are what running `lratdirect` on every job and seeing `s VERIFIED UNSAT` shows,
given that the executable computes `checkJob` on the blocks it read (its IO loop and the compiled
code are trusted; the proof bytes and the parser are not). Name lookup needs the names to be
distinct, which is `CnfRuns.names_nodup`. Axioms: the standard three.
-/

namespace DirectRuns
open CnfGen CnfSpecs CnfRuns CircuitDual Mod3SemBounds Garden.LratDirect

/-- With distinct names, looking a member up by its name finds it. -/
theorem find?_name {α : Type} (nm : α → String) (l : List α) (hnd : (l.map nm).Nodup) {x : α}
    (hx : x ∈ l) : l.find? (fun y => nm y == nm x) = some x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · have hne : nm y ≠ nm x := fun h => hnd.1 (h ▸ List.mem_map_of_mem hx')
      rw [ih hnd.2 hx']
      split <;> simp_all

theorem scanSpec?_of_mem {x : ScanSpec} (hx : x ∈ scanList) : scanSpec? x.name = some x :=
  find?_name (fun y : ScanSpec => y.name) scanList names_nodup.1 hx

theorem splitSpec?_of_mem {x : SplitSpec} (hx : x ∈ splitList) : splitSpec? x.name = some x :=
  find?_name (fun y : SplitSpec => y.name) splitList names_nodup.2 hx

/-- A scan hypothesis from `checkJob` at every `r` of its range. -/
theorem scanUnsat_direct {x : ScanSpec} (hx : x ∈ scanList)
    (h : ∀ r, x.lo ≤ r → r ≤ x.hi → ∃ bs, (checkJob (.scan x.name r) bs).verified = true) :
    ScanUnsat x.run x.lo x.hi := by
  intro r hlo hhi
  obtain ⟨bs, hc⟩ := h r hlo hhi
  exact scan_sound (scanSpec?_of_mem hx) hlo hhi bs hc

/-- A split-run hypothesis from `checkJob` at every leaf index. -/
theorem leavesUnsat_direct {x : SplitSpec} (hx : x ∈ splitList)
    (h : ∀ i < x.leaves.length, ∃ bs, (checkJob (.leaf x.name i) bs).verified = true) :
    LeavesUnsat x.run x.r x.leaves := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨bs, hc⟩ := h i hi
  exact leaf_sound (splitSpec?_of_mem hx) (List.getElem?_eq_getElem hi) bs hc

/-- **The theorem, from `lratdirect`'s checking function.** -/
theorem mod3_6_size_13_direct
    (hS : ∀ x ∈ scanList, ∀ r, x.lo ≤ r → r ≤ x.hi →
      ∃ bs, (checkJob (.scan x.name r) bs).verified = true)
    (hL : ∀ x ∈ splitList, ∀ i < x.leaves.length,
      ∃ bs, (checkJob (.leaf x.name i) bs).verified = true) :
    (LB 6 (mod3 1) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 1 gs) ∧
      (LB 6 (mod3 2) 13 ∧ ∃ gs : List Gate, gs.length = 13 ∧ Computes 2 gs) :=
  mod3_6_size_13_lists (fun x hx => scanUnsat_direct hx (hS x hx))
    (fun x hx => leavesUnsat_direct hx (hL x hx))

end DirectRuns
