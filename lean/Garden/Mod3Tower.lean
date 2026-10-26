/-
# size(MOD3^1_6) ≥ 13 from the SAT runs alone: the smaller sizes discharged

`Mod3Lower.mod3_6_lower` assumed the smaller sizes `sem` and `elim` use (`LB 5 (mod3 q) (c5 q)`,
`LB 4 (mod3 q) (c4 q)`, `LB 5 w2 10`). Each is itself a SAT result, under its own option set, and
the `w2` runs' `semrows` use smaller sizes again. This file proves every level of that tower from
its own runs (`Tower.lower`), down to runs with no `elim`/`sem` bounds at all, so the final
theorem's only hypotheses are the runs' SAT sides.

The runs (`research/log/2026-10-24-2053.md` has the full table; each option set was confirmed by
regenerating the CNF and matching its clause count, or the ledger's DIMACS sha256):

| function | gates refuted | results file | `Opts` |
|---|---|---|---|
| `MOD3_3^q` | 1–2, 1–3, 1–3 | `results_small.out`, `results_mod3_34_lean.out` | `best 3` |
| `MOD3_4^q` | 1–6, 1–6, 1–5 | `results_small.out`, `results_mod3_34_lean.out` | `best 4` |
| `MOD3_5^0`, `MOD3_5^2` | 1–8; 9 | `results_mod3_5_{0,2}_r1-8*.out`; `*_r9_cubes.out` | `best 5`; `cube5` |
| `MOD3_5^1` | 1–8 | `results_5in.out`, `results_mod3_5_1_r1-8_lean.out` | `best 5` |
| `w2_3^q`, `w2_4^0`, `w2_4^1`, `pq` | 1–3, 1–3, 1–2, 1–6, 1–5, 1–6 | `results_w2_5_1_restricted.out` | `restr` |
| `w2_5^1` | 1–7; 8; 9 | `results_w2_5_1_scan.out`; ledgers `w2_5_1_{8,9}_w2_s1` | `w2best`; `w2cube` |
| `MOD3_6^1` | 1–11; 12 | `results_mod3_6_1_elim.out`; the r = 12 ledgers | `elim6`; `full6` |

Proved (axioms: the standard three):
* `lb3`, `lb4`, `lb5`, `lbr`, `lbw2`, `lb6`: each level from its runs and the levels below.
* **`mod3_6_lower_sat`**: `LB 6 (mod3 1) 13` from the 22 `NoAdm` hypotheses above and nothing else.
  `mod3_2_6_lower_sat`: the same for `MOD3^2_6`, through `CircuitDual.mod3_6_size_dual`.
* `full6_iff`: the r = 12 run's `Adm` is exactly `Mod3Lower.Admissible`, so that hypothesis is
  the one `Mod3Lower` read against the CNF field by field.
* `full6_sat13` (positive control): under the same hypotheses some 13-gate circuit satisfies the
  r = 12 run's `Adm`, so that hypothesis says something about 12 gates, not about every size.
* `tables`: the restricted functions here have the truth tables `results_w2_5_1_restricted.out`
  scanned.

Still outside the kernel, per run: that every `Adm` circuit of `r` gates satisfies that run's CNF
for `r` (read by eye; the fields are the clause families), and that the CNF is unsatisfiable
(LRAT checked by Lean's verified checker through `lratcheck`'s parser and IO loop, for every run;
`results_small.out` and `results_5in.out` were first checked by the Python DRUP checker and
rerun through Lean in `results_mod3_34_lean.out` and `results_mod3_5_1_r1-8_lean.out`; plus the
cube covers).
-/
import Garden.W2SemBounds

namespace Mod3Tower
open CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds Mod3Lower Tower W2SemBounds

/-! ### The runs' option sets -/

/-- `best_opts` for a fully symmetric target on `n` inputs: `order`, `allin`, `first01`,
`distinct` (and `sym`). -/
def best (n : ℕ) : Opts where
  S := (· < n)
  symin := false
  table := false
  first01 := true
  allin := true
  elim := none
  elim2 := none
  sem := fun _ _ => False

/-- `cubes.py`'s base at n = 5, r = 9: `best_opts` plus the table clause. -/
def cube5 : Opts := { best 5 with table := true }

/-- `best_opts` plus `ELIM=1` at n = 6, q = 1: `B_c = r − size(MOD3_5^{(1 − c) mod 3})`. -/
def elim6 : Opts := { best 6 with elim := some (fun c => c5 ((4 - c.toNat) % 3)) }

/-- The r = 12 run's `sem` (|S| = 1, 2), `semxor` and `semeq` row sets, with the sizes
`Mod3SemBounds` proves them for. -/
def sem6 (T : Set (List Bool)) (s : ℕ) : Prop :=
  (∃ v < 6, ∃ c : Bool, T = rows1 6 v c ∧ s = c5 ((4 - c.toNat) % 3)) ∨
  (∃ u < 6, ∃ v < 6, u < v ∧ ∃ a b : Bool, T = rows2 6 u v a b ∧
    s = c4 ((7 - a.toNat - b.toNat) % 3)) ∨
  (∃ u < 6, ∃ v < 6, u < v ∧
    T = {x | x.length = 6 ∧ x.getD u false = (true ^^ x.getD v false)} ∧ s = c4 0) ∨
  (∃ u < 6, ∃ v < 6, u < v ∧
    T = {x | x.length = 6 ∧ x.getD u false = (false ^^ x.getD v false)} ∧ s = 10)

/-- The r = 12 run: `best_opts`, `ELIM=1 ELIM2=1 SEM=1,2 SEMXOR=1 SYMIN=1 SEMEQ=1`, and
`cubes.py`'s table clause. -/
def full6 : Opts :=
  { best 6 with
    symin := true
    table := true
    elim := some fun c => c5 ((4 - c.toNat) % 3)
    elim2 := some fun a b => c4 ((7 - a.toNat - b.toNat) % 3)
    sem := sem6 }

/-- `_restricted_size`'s scans: `sym`, `order`, `distinct` and nothing else (`allin` off). -/
def restr : Opts where
  S := fun _ => False
  symin := false
  table := false
  first01 := false
  allin := false
  elim := none
  elim2 := none
  sem := fun _ _ => False

/-- `w2_5^1`'s symmetric inputs, `x1 … x4`. -/
def W : ℕ → Prop := fun i => 1 ≤ i ∧ i < 5

/-- `best_opts` for `w2_5^1`, which is not fully symmetric: `order`, `allin`, `distinct`. -/
def w2best : Opts := { restr with S := W, allin := true }

/-- `w2cubes.py`'s base: `best_opts`, `symvars = (1, 2, 3, 4)` (`symin` and the table clause on
`W`), and `semrows = sem_general(|S| = 1, 2) + sem_pairs`. -/
def w2cube : Opts :=
  { w2best with
    symin := true
    table := true
    sem := fun T s => semGen T s ∨ semPairs T s }

/-! ### Soundness of each run's added constraints -/

theorem sound_best (n : ℕ) (f : List Bool → Bool) : Sound n f (· < n) (best n) :=
  sound_plain n f _ _ rfl (fun _ _ hu => hu) (fun _ _ h => h) rfl rfl

theorem sound_cube5 (f : List Bool → Bool) : Sound 5 f (· < 5) cube5 :=
  sound_plain 5 f _ _ rfl (fun _ _ hu => hu) (fun _ _ h => h) rfl rfl

theorem sound_restr (n : ℕ) (f : List Bool → Bool) : Sound n f (fun _ => False) restr :=
  sound_plain n f _ _ rfl (fun h => by cases h) (fun _ _ h => h) rfl rfl

theorem sound_w2best : Sound 5 w2 W w2best :=
  sound_plain 5 w2 _ _ rfl (fun h => by cases h) (fun _ _ h => h) rfl rfl

theorem sound_w2cube
    (h3 : ∀ q < 3, LB 3 (mod3 q) (c3 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw3 : ∀ q < 3, LB 3 (wq q) (cw3 q)) (hw40 : LB 4 (wq 0) 7) (hw41 : LB 4 (wq 1) 6)
    (hpq : LB 4 pq 7) : Sound 5 w2 W w2cube where
  S_eq := rfl
  first01 := fun h => by cases h
  sem := w2_sem_bounds h3 h4 hw3 hw40 hw41 hpq
  elim := fun e h => by cases h
  elim2 := fun e h => by cases h

theorem sound_elim6 (h5 : ∀ q < 3, LB 5 (mod3 q) (c5 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw : LB 5 w2 10) : Sound 6 (mod3 1) (· < 6) elim6 where
  S_eq := rfl
  first01 := fun _ u hu => hu
  sem := fun _ _ h => h.elim
  elim := fun e he v hv c => by
    cases he
    exact ⟨fun x hx => hx.1, fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).1 v hv c⟩
  elim2 := fun e h => by cases h

theorem sound_full6 (h5 : ∀ q < 3, LB 5 (mod3 q) (c5 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw : LB 5 w2 10) : Sound 6 (mod3 1) (· < 6) full6 where
  S_eq := rfl
  first01 := fun _ u hu => hu
  sem := by
    rintro T s (⟨v, hv, c, rfl, rfl⟩ | ⟨u, hu, v, hv, huv, a, b, rfl, rfl⟩ |
      ⟨u, hu, v, hv, huv, rfl, rfl⟩ | ⟨u, hu, v, hv, huv, rfl, rfl⟩)
    · exact ⟨fun x hx => hx.1, fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).1 v hv c⟩
    · exact ⟨fun x hx => hx.1,
        fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).2.1 u hu v hv huv a b⟩
    · exact ⟨fun x hx => hx.1,
        fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).2.2.1 u hu v hv huv⟩
    · exact ⟨fun x hx => hx.1,
        fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).2.2.2 u hu v hv huv⟩
  elim := fun e he v hv c => by
    cases he
    exact ⟨fun x hx => hx.1, fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).1 v hv c⟩
  elim2 := fun e he u hu v hv huv a b => by
    cases he
    exact ⟨fun x hx => hx.1,
      fun gs hne hgs => (mod3_6_1_sem_bounds h5 h4 hw gs hne hgs).2.1 u hu v hv huv a b⟩

/-! ### Finite facts, by `decide` -/

set_option synthInstance.maxSize 1024

theorem facts3 : ∀ q < 3,
    (∀ u < 3, ∀ v < 3, u < 3 → v < 3 → ∀ z ∈ allRows 3, mod3 q (swapIn u v z) = mod3 q z) ∧
    (∀ c : Bool, ∃ x ∈ allRows 3, mod3 q x ≠ c) ∧
    (∀ u < 3, ∀ b : Bool, ∃ x ∈ allRows 3, mod3 q x ≠ (b ^^ x.getD u false)) ∧
    (∀ c : Bool, ∃ x ∈ allRows 3, wq q x ≠ c) ∧
    (∀ u < 3, ∀ b : Bool, ∃ x ∈ allRows 3, wq q x ≠ (b ^^ x.getD u false)) := by
  decide +kernel

theorem facts4 : ∀ q < 3,
    (∀ u < 4, ∀ v < 4, u < 4 → v < 4 → ∀ z ∈ allRows 4, mod3 q (swapIn u v z) = mod3 q z) ∧
    (∀ c : Bool, ∃ x ∈ allRows 4, mod3 q x ≠ c) ∧
    (∀ u < 4, ∀ b : Bool, ∃ x ∈ allRows 4, mod3 q x ≠ (b ^^ x.getD u false)) := by
  decide +kernel

theorem facts4w : (∀ q < 2, (∀ c : Bool, ∃ x ∈ allRows 4, wq q x ≠ c) ∧
      (∀ u < 4, ∀ b : Bool, ∃ x ∈ allRows 4, wq q x ≠ (b ^^ x.getD u false))) ∧
    (∀ c : Bool, ∃ x ∈ allRows 4, pq x ≠ c) ∧
    (∀ u < 4, ∀ b : Bool, ∃ x ∈ allRows 4, pq x ≠ (b ^^ x.getD u false)) := by
  decide +kernel

theorem facts5 : ∀ q < 3,
    (∀ u < 5, ∀ v < 5, u < 5 → v < 5 → ∀ z ∈ allRows 5, mod3 q (swapIn u v z) = mod3 q z) ∧
    (∀ c : Bool, ∃ x ∈ allRows 5, mod3 q x ≠ c) ∧
    (∀ u < 5, ∀ b : Bool, ∃ x ∈ allRows 5, mod3 q x ≠ (b ^^ x.getD u false)) := by
  decide +kernel

theorem facts_w2 : (∀ c : Bool, ∃ x ∈ allRows 5, w2 x ≠ c) ∧
    (∀ u < 5, ∀ b : Bool, ∃ x ∈ allRows 5, w2 x ≠ (b ^^ x.getD u false)) := by
  decide +kernel

/-- A truth table as `optimal_circuit.tt_of` writes it: row `t`, input `i` = bit `i` of `t`. -/
def ttStr (m : ℕ) (f : List Bool → Bool) : String :=
  String.ofList ((List.range (2 ^ m)).map fun t =>
    if f ((List.range m).map fun i => t.testBit i) then '1' else '0')

/-- The restricted functions are the tables `results_w2_5_1_restricted.out` scanned. -/
theorem tables : ttStr 3 (wq 0) = "10010100" ∧ ttStr 3 (wq 1) = "00101001" ∧
    ttStr 3 (wq 2) = "01000010" ∧ ttStr 4 (wq 0) = "1001010001000010" ∧
    ttStr 4 (wq 1) = "0010100110010100" ∧ ttStr 4 pq = "0001100010000110" := by
  decide +kernel

/-! ### The tower -/

/-- `MOD3_3^q ≥ 3, 4, 4` (`results_small.out`, `results_mod3_34_lean.out`). -/
theorem lb3 (h0 : NoAdm 3 (mod3 0) (best 3) 1 2) (h1 : NoAdm 3 (mod3 1) (best 3) 1 3)
    (h2 : NoAdm 3 (mod3 2) (best 3) 1 3) : ∀ q < 3, LB 3 (mod3 q) (c3 q) := by
  intro q hq
  obtain ⟨hs, hc, hl, -, -⟩ := facts3 q hq
  have L := fun s => lower1 3 (mod3 q) (· < 3) (fun _ h => h)
    (symOn_of 3 _ (fun _ h => h) _ hs) (nonconst_of 3 _ hc) (nonlit_of 3 _ hl) (best 3)
    (sound_best 3 _) s
  interval_cases q
  exacts [L 3 h0, L 4 h1, L 4 h2]

/-- `MOD3_4^q ≥ 7, 7, 6` (`results_small.out`, `results_mod3_34_lean.out`). -/
theorem lb4 (h0 : NoAdm 4 (mod3 0) (best 4) 1 6) (h1 : NoAdm 4 (mod3 1) (best 4) 1 6)
    (h2 : NoAdm 4 (mod3 2) (best 4) 1 5) : ∀ q < 3, LB 4 (mod3 q) (c4 q) := by
  intro q hq
  obtain ⟨hs, hc, hl⟩ := facts4 q hq
  have L := fun s => lower1 4 (mod3 q) (· < 4) (fun _ h => h)
    (symOn_of 4 _ (fun _ h => h) _ hs) (nonconst_of 4 _ hc) (nonlit_of 4 _ hl) (best 4)
    (sound_best 4 _) s
  interval_cases q
  exacts [L 7 h0, L 7 h1, L 6 h2]

/-- `MOD3_5^q ≥ 10, 9, 10` (r ≤ 8 scans; r = 9 cube runs for q = 0, 2). -/
theorem lb5 (h0 : NoAdm 5 (mod3 0) (best 5) 1 8) (h0c : NoAdm 5 (mod3 0) cube5 9 9)
    (h1 : NoAdm 5 (mod3 1) (best 5) 1 8) (h2 : NoAdm 5 (mod3 2) (best 5) 1 8)
    (h2c : NoAdm 5 (mod3 2) cube5 9 9) : ∀ q < 3, LB 5 (mod3 q) (c5 q) := by
  intro q hq
  obtain ⟨hs, hc, hl⟩ := facts5 q hq
  have hsym := symOn_of 5 _ (fun _ h => h) _ hs
  interval_cases q
  · exact lower2 5 _ _ (fun _ h => h) hsym (nonconst_of 5 _ hc) (nonlit_of 5 _ hl) (best 5) cube5
      (sound_best 5 _) (sound_cube5 _) 8 10 h0 h0c
  · exact lower1 5 _ _ (fun _ h => h) hsym (nonconst_of 5 _ hc) (nonlit_of 5 _ hl) (best 5)
      (sound_best 5 _) 9 h1
  · exact lower2 5 _ _ (fun _ h => h) hsym (nonconst_of 5 _ hc) (nonlit_of 5 _ hl) (best 5) cube5
      (sound_best 5 _) (sound_cube5 _) 8 10 h2 h2c

/-- The restricted functions of the `w2_5^1` runs (`results_w2_5_1_restricted.out`). -/
theorem lbr (hw3_0 : NoAdm 3 (wq 0) restr 1 3) (hw3_1 : NoAdm 3 (wq 1) restr 1 3)
    (hw3_2 : NoAdm 3 (wq 2) restr 1 2) (hw4_0 : NoAdm 4 (wq 0) restr 1 6)
    (hw4_1 : NoAdm 4 (wq 1) restr 1 5) (hpq : NoAdm 4 pq restr 1 6) :
    (∀ q < 3, LB 3 (wq q) (cw3 q)) ∧ LB 4 (wq 0) 7 ∧ LB 4 (wq 1) 6 ∧ LB 4 pq 7 := by
  have hS : ∀ n u : ℕ, (fun _ => False) u → u < n := fun _ _ h => h.elim
  have hsym : ∀ (n : ℕ) (f : List Bool → Bool), SymOn n (fun _ => False) f :=
    fun _ _ _ _ hu => hu.elim
  obtain ⟨hw4, hpc, hpl⟩ := facts4w
  refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, hc, hl⟩ := facts3 q hq
    have L := fun s => lower1 3 (wq q) _ (hS 3) (hsym 3 _) (nonconst_of 3 _ hc) (nonlit_of 3 _ hl)
      restr (sound_restr 3 _) s
    interval_cases q
    exacts [L 4 hw3_0, L 4 hw3_1, L 3 hw3_2]
  · exact lower1 4 _ _ (hS 4) (hsym 4 _) (nonconst_of 4 _ (hw4 0 (by omega)).1)
      (nonlit_of 4 _ (hw4 0 (by omega)).2) restr (sound_restr 4 _) 7 hw4_0
  · exact lower1 4 _ _ (hS 4) (hsym 4 _) (nonconst_of 4 _ (hw4 1 (by omega)).1)
      (nonlit_of 4 _ (hw4 1 (by omega)).2) restr (sound_restr 4 _) 6 hw4_1
  · exact lower1 4 _ _ (hS 4) (hsym 4 _) (nonconst_of 4 _ hpc) (nonlit_of 4 _ hpl) restr
      (sound_restr 4 _) 7 hpq

/-- `size(w2_5^1) ≥ 10` (`W2_LOWER`): r ≤ 7 by the scan, r = 8, 9 by `w2cubes.py`. -/
theorem lbw2 (h3 : ∀ q < 3, LB 3 (mod3 q) (c3 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw3 : ∀ q < 3, LB 3 (wq q) (cw3 q)) (hw40 : LB 4 (wq 0) 7) (hw41 : LB 4 (wq 1) 6)
    (hpq : LB 4 pq 7) (hs : NoAdm 5 w2 w2best 1 7) (h8 : NoAdm 5 w2 w2cube 8 8)
    (h9 : NoAdm 5 w2 w2cube 9 9) : LB 5 w2 10 :=
  lower2 5 w2 W (fun _ h => h.2) w2_sym (nonconst_of 5 _ facts_w2.1) (nonlit_of 5 _ facts_w2.2)
    w2best w2cube sound_w2best (sound_w2cube h3 h4 hw3 hw40 hw41 hpq) 7 10 hs
    (noAdm_join 5 w2 w2cube 8 8 9 h8 h9)

/-- `MOD3_6^1 ≥ 13` from its two runs, given the sizes they used. -/
theorem lb6 (h5 : ∀ q < 3, LB 5 (mod3 q) (c5 q)) (h4 : ∀ q < 3, LB 4 (mod3 q) (c4 q))
    (hw : LB 5 w2 10) (h6 : NoAdm 6 (mod3 1) elim6 1 11) (h12 : NoAdm 6 (mod3 1) full6 12 12) :
    LB 6 (mod3 1) 13 :=
  lower2 6 (mod3 1) (· < 6) (fun _ h => h) mod3_sym mod3_nonconst mod3_nonlit elim6 full6
    (sound_elim6 h5 h4 hw) (sound_full6 h5 h4 hw) 11 13 h6 h12

/-- **`size(MOD3^1_6) ≥ 13`, from the SAT runs alone.** Each hypothesis says that no circuit with
the given number of gates satisfies one run's `Adm`, which is what that run's CNF refutation
certifies; there is one per run, and no other hypothesis. -/
theorem mod3_6_lower_sat
    -- `results_small.out`, rerun through Lean in `results_mod3_34_lean.out`
    (h3_0 : NoAdm 3 (mod3 0) (best 3) 1 2) (h3_1 : NoAdm 3 (mod3 1) (best 3) 1 3)
    (h3_2 : NoAdm 3 (mod3 2) (best 3) 1 3)
    (h4_0 : NoAdm 4 (mod3 0) (best 4) 1 6) (h4_1 : NoAdm 4 (mod3 1) (best 4) 1 6)
    (h4_2 : NoAdm 4 (mod3 2) (best 4) 1 5)
    -- `results_mod3_5_0_r1-8.out`, `results_mod3_5_0_r9_cubes.out`
    (h5_0 : NoAdm 5 (mod3 0) (best 5) 1 8) (h5_0c : NoAdm 5 (mod3 0) cube5 9 9)
    -- `results_5in.out` (and `results_mod3_5_1_r1-8_lean.out`)
    (h5_1 : NoAdm 5 (mod3 1) (best 5) 1 8)
    -- `results_mod3_5_2_r1-8_lean.out`, `results_mod3_5_2_r9_cubes.out`
    (h5_2 : NoAdm 5 (mod3 2) (best 5) 1 8) (h5_2c : NoAdm 5 (mod3 2) cube5 9 9)
    -- `results_w2_5_1_restricted.out`
    (hw3_0 : NoAdm 3 (wq 0) restr 1 3) (hw3_1 : NoAdm 3 (wq 1) restr 1 3)
    (hw3_2 : NoAdm 3 (wq 2) restr 1 2) (hw4_0 : NoAdm 4 (wq 0) restr 1 6)
    (hw4_1 : NoAdm 4 (wq 1) restr 1 5) (hpq : NoAdm 4 pq restr 1 6)
    -- `results_w2_5_1_scan.out`, `ledger_w2_5_1_8_w2_s1.txt`, `ledger_w2_5_1_9_w2_s1.txt`
    (hw_s : NoAdm 5 w2 w2best 1 7) (hw_8 : NoAdm 5 w2 w2cube 8 8) (hw_9 : NoAdm 5 w2 w2cube 9 9)
    -- `results_mod3_6_1_elim.out`, the r = 12 ledgers (`r12_status.py`)
    (h6 : NoAdm 6 (mod3 1) elim6 1 11) (h12 : NoAdm 6 (mod3 1) full6 12 12) :
    LB 6 (mod3 1) 13 := by
  have L3 := lb3 h3_0 h3_1 h3_2
  have L4 := lb4 h4_0 h4_1 h4_2
  have L5 := lb5 h5_0 h5_0c h5_1 h5_2 h5_2c
  obtain ⟨R3, R40, R41, Rpq⟩ := lbr hw3_0 hw3_1 hw3_2 hw4_0 hw4_1 hpq
  exact lb6 L5 L4 (lbw2 L3 L4 R3 R40 R41 Rpq hw_s hw_8 hw_9) h6 h12

/-- `CircuitDual.Computes` (rows as `Fin 6 → Bool`) is `LB`'s form (rows as lists of length 6). -/
lemma computes_iff (r : ℕ) (gs : List Gate) :
    Computes r gs ↔ (gs ≠ [] ∧ ∀ y : List Bool, y.length = 6 → out y gs = mod3 r y) := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x : Fin 6 → Bool, List.ofFn x = y :=
      ⟨fun i => y.getD i false, by
        apply List.ext_getElem (by simp [hy])
        intro i h1 h2
        rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]⟩
    exact h x
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun x => h _ (by simp)⟩

/-- **`size(MOD3^2_6) ≥ 13`**, under the same hypotheses: a circuit for `MOD3^2_6` gives one of
the same length for `MOD3^1_6` (`CircuitDual.mod3_6_size_dual`). -/
theorem mod3_2_6_lower_sat
    (h3_0 : NoAdm 3 (mod3 0) (best 3) 1 2) (h3_1 : NoAdm 3 (mod3 1) (best 3) 1 3)
    (h3_2 : NoAdm 3 (mod3 2) (best 3) 1 3)
    (h4_0 : NoAdm 4 (mod3 0) (best 4) 1 6) (h4_1 : NoAdm 4 (mod3 1) (best 4) 1 6)
    (h4_2 : NoAdm 4 (mod3 2) (best 4) 1 5)
    (h5_0 : NoAdm 5 (mod3 0) (best 5) 1 8) (h5_0c : NoAdm 5 (mod3 0) cube5 9 9)
    (h5_1 : NoAdm 5 (mod3 1) (best 5) 1 8)
    (h5_2 : NoAdm 5 (mod3 2) (best 5) 1 8) (h5_2c : NoAdm 5 (mod3 2) cube5 9 9)
    (hw3_0 : NoAdm 3 (wq 0) restr 1 3) (hw3_1 : NoAdm 3 (wq 1) restr 1 3)
    (hw3_2 : NoAdm 3 (wq 2) restr 1 2) (hw4_0 : NoAdm 4 (wq 0) restr 1 6)
    (hw4_1 : NoAdm 4 (wq 1) restr 1 5) (hpq : NoAdm 4 pq restr 1 6)
    (hw_s : NoAdm 5 w2 w2best 1 7) (hw_8 : NoAdm 5 w2 w2cube 8 8) (hw_9 : NoAdm 5 w2 w2cube 9 9)
    (h6 : NoAdm 6 (mod3 1) elim6 1 11) (h12 : NoAdm 6 (mod3 1) full6 12 12) :
    LB 6 (mod3 2) 13 := by
  intro gs hne hgs
  obtain ⟨gs', hlen, hc⟩ := (mod3_6_size_dual gs).2 ((computes_iff 2 gs).mpr ⟨hne, hgs⟩)
  rw [← hlen]
  exact mod3_6_lower_sat h3_0 h3_1 h3_2 h4_0 h4_1 h4_2 h5_0 h5_0c h5_1 h5_2 h5_2c hw3_0 hw3_1
    hw3_2 hw4_0 hw4_1 hpq hw_s hw_8 hw_9 h6 h12 gs' ((computes_iff 1 gs').mp hc).1
    ((computes_iff 1 gs').mp hc).2

/-- **Positive control (conditional): the r = 12 hypothesis is not about every size.** Under the same hypotheses, the
r = 12 run's `Adm` is satisfied by a 13-gate circuit (a minimum one, from the 13-gate circuit of
`Mod3Upper`), so `NoAdm 6 (mod3 1) full6 13 13` is false: the clause families of the r = 12 run do
not exclude every circuit, only (by hypothesis) the 12-gate ones. The Lean counterpart of the SAT
control `r13_decode.py`. -/
theorem full6_sat13
    (h3_0 : NoAdm 3 (mod3 0) (best 3) 1 2) (h3_1 : NoAdm 3 (mod3 1) (best 3) 1 3)
    (h3_2 : NoAdm 3 (mod3 2) (best 3) 1 3)
    (h4_0 : NoAdm 4 (mod3 0) (best 4) 1 6) (h4_1 : NoAdm 4 (mod3 1) (best 4) 1 6)
    (h4_2 : NoAdm 4 (mod3 2) (best 4) 1 5)
    (h5_0 : NoAdm 5 (mod3 0) (best 5) 1 8) (h5_0c : NoAdm 5 (mod3 0) cube5 9 9)
    (h5_1 : NoAdm 5 (mod3 1) (best 5) 1 8)
    (h5_2 : NoAdm 5 (mod3 2) (best 5) 1 8) (h5_2c : NoAdm 5 (mod3 2) cube5 9 9)
    (hw3_0 : NoAdm 3 (wq 0) restr 1 3) (hw3_1 : NoAdm 3 (wq 1) restr 1 3)
    (hw3_2 : NoAdm 3 (wq 2) restr 1 2) (hw4_0 : NoAdm 4 (wq 0) restr 1 6)
    (hw4_1 : NoAdm 4 (wq 1) restr 1 5) (hpq : NoAdm 4 pq restr 1 6)
    (hw_s : NoAdm 5 w2 w2best 1 7) (hw_8 : NoAdm 5 w2 w2cube 8 8) (hw_9 : NoAdm 5 w2 w2cube 9 9)
    (h6 : NoAdm 6 (mod3 1) elim6 1 11) (h12 : NoAdm 6 (mod3 1) full6 12 12) :
    ¬ NoAdm 6 (mod3 1) full6 13 13 := by
  have L3 := lb3 h3_0 h3_1 h3_2
  have L4 := lb4 h4_0 h4_1 h4_2
  have L5 := lb5 h5_0 h5_0c h5_1 h5_2 h5_2c
  obtain ⟨R3, R40, R41, Rpq⟩ := lbr hw3_0 hw3_1 hw3_2 hw4_0 hw4_1 hpq
  have Lw := lbw2 L3 L4 R3 R40 R41 Rpq hw_s hw_8 hw_9
  have L := lb6 L5 L4 Lw h6 h12
  have hc := (computes_iff 1 Mod3Upper.c13).mp Mod3Upper.mod3_1_upper
  obtain ⟨gs, o, neg, hl, hadm⟩ := exists_adm 6 (mod3 1) (· < 6) (fun _ h => h) mod3_sym
    mod3_nonconst mod3_nonlit Mod3Upper.c13 hc
    (fun gs' h => by rw [Mod3Upper.c13_length]; exact L gs' h.1 h.2)
  have hl13 : gs.length = 13 := by rw [hl, Mod3Upper.c13_length]
  intro hno
  exact hno gs o neg (by omega) (by omega) (hadm full6 (sound_full6 L5 L4 Lw))

/-! ### The r = 12 hypothesis is the one `Mod3Lower` checked -/

/-- `Adm 6 (mod3 1) full6` is `Mod3Lower.Admissible`, field for field. -/
theorem full6_iff (gs : List Gate) (o : ℕ) (neg : Bool) :
    Adm 6 (mod3 1) full6 gs o neg ↔ Admissible gs o neg := by
  constructor
  · intro h
    have sem := h.sem
    exact
      { shaped := h.shaped, normal := h.normal, out_lo := h.out_lo, out_hi := h.out_hi,
        computes := h.computes, nondegenerate := h.nondegenerate, used := h.used,
        order := h.order, symin := h.symin rfl,
        first01_table := fun h0 => ⟨(h.first01 rfl h0).1, (h.first01 rfl h0).2,
          h.table rfl h0 (by rw [(h.first01 rfl h0).1]; show 0 < 6; omega)
            (by rw [(h.first01 rfl h0).2]; show 1 < 6; omega)⟩,
        allin := fun u hu => h.allin rfl u hu (mod3_essential u hu),
        distinct := h.distinct,
        elim := h.elim _ rfl, elim2 := h.elim2 _ rfl,
        sem1 := fun v hv c => sem _ _ (show sem6 _ _ from Or.inl ⟨v, hv, c, rfl, rfl⟩),
        sem2 := fun u hu v hv huv a b => sem _ _ (show sem6 _ _ from Or.inr (Or.inl ⟨u, hu, v, hv, huv, a, b, rfl, rfl⟩)),
        semxor := fun u hu v hv huv => sem _ _ (show sem6 _ _ from Or.inr (Or.inr (Or.inl ⟨u, hu, v, hv, huv, rfl, rfl⟩))),
        semeq := fun u hu v hv huv => sem _ _ (show sem6 _ _ from Or.inr (Or.inr (Or.inr ⟨u, hu, v, hv, huv, rfl, rfl⟩))) }
  · intro h
    exact
      { shaped := h.shaped, normal := h.normal, out_lo := h.out_lo, out_hi := h.out_hi,
        computes := h.computes, nondegenerate := h.nondegenerate, used := h.used,
        order := h.order, distinct := h.distinct,
        symin := fun _ => h.symin,
        table := fun _ h0 _ _ => (h.first01_table h0).2.2,
        first01 := fun _ h0 => ⟨(h.first01_table h0).1, (h.first01_table h0).2.1⟩,
        allin := fun _ u hu _ => h.allin u hu,
        elim := fun e he => by cases he; exact h.elim,
        elim2 := fun e he => by cases he; exact h.elim2,
        sem := by
          rintro T s (⟨v, hv, c, rfl, rfl⟩ | ⟨u, hu, v, hv, huv, a, b, rfl, rfl⟩ |
            ⟨u, hu, v, hv, huv, rfl, rfl⟩ | ⟨u, hu, v, hv, huv, rfl, rfl⟩)
          · exact h.sem1 v hv c
          · exact h.sem2 u hu v hv huv a b
          · exact h.semxor u hu v hv huv
          · exact h.semeq u hu v hv huv }

end Mod3Tower
