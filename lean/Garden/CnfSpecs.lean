import Garden.CnfGen
import Garden.CnfLeaves

/-!
# The 22 runs' encodings, as `CnfGen` options

Each run of `Mod3Tower.mod3_6_lower_sat` as the arguments its Python code passed to
`optimal_circuit.encode` (`best_opts`, `_restricted_size`, `ELIM=1`, `cubes.base`, `w2cubes.base`),
and its cube splits. `Std` only, for the exporter. The truth tables are Python's `tt_of`; that
they are the Lean functions `CircuitDual.mod3`, `W2SemBounds.wq`, `pq` is proved in `CnfRuns`.
-/

namespace CnfSpecs
open CnfGen

/-! ### Truth tables (`tt_of`): row `t`, input `i` = bit `i` of `t` -/

def bit (t v : Nat) : Nat := (t.testBit v).toNat

/-- `MOD3_n^q`: `int(sum(x) % 3 == q)`. -/
def mod3T (q n : Nat) (t : Nat) : Bool := ((List.range n).map (bit t)).sum % 3 == q

/-- `w2_m^q`: `int((2 * x[0] + sum(x[1:])) % 3 == q)`. -/
def wqT (q n : Nat) (t : Nat) : Bool := (2 * bit t 0 + ((List.range' 1 (n - 1)).map (bit t)).sum) % 3 == q

/-- `[2 y0 + 2 y1 + y2 + y3 ≡ 1 mod 3]` (`W2SemBounds.pq`). -/
def pqT (t : Nat) : Bool := (2 * bit t 0 + 2 * bit t 1 + bit t 2 + bit t 3) % 3 == 1

/-! ### Sizes the bounds subtract (`CERTIFIED`, `W2_LOWER`, `_restricted_size`) -/

def c4 (q : Nat) : Nat := [7, 7, 6].getD q 0
def c5 (q : Nat) : Nat := [10, 9, 10].getD q 0
def c3 (q : Nat) : Nat := [3, 4, 4].getD q 0
def cw3 (q : Nat) : Nat := [4, 4, 3].getD q 0
def sW1 (v : Nat) (c : Bool) : Nat := if v = 0 then (if c then 6 else 7) else (if c then 7 else 6)
def sW2 (u : Nat) (a b : Bool) : Nat :=
  if u = 0 then c3 ((7 - 2 * a.toNat - b.toNat) % 3) else cw3 ((7 - a.toNat - b.toNat) % 3)
def sWP (u : Nat) (c : Bool) : Nat := if u = 0 then (if c then 7 else 4) else (if c then 4 else 7)

/-! ### Row sets of the `redundancy` calls -/

def rowsWhere (n : Nat) (p : Nat → Bool) : List Nat := (rows n).filter p

/-- `sem`, |S| = 1: rows `x_v = c`, size `s c`. -/
def sem1Rows (n : Nat) (s : Nat → Bool → Nat) : List (List Nat × Nat) :=
  (List.range n).flatMap fun v => [false, true].map fun c => (rowsWhere n fun t => t.testBit v == c, s v c)

/-- `sem`, |S| = 2: rows `x_u = a, x_v = b`, `u < v`, size `s u a b`. -/
def sem2Rows (n : Nat) (s : Nat → Bool → Bool → Nat) : List (List Nat × Nat) :=
  (combs 2 (List.range n)).flatMap fun c =>
    match c with
    | [u, v] => [(false, false), (false, true), (true, false), (true, true)].map fun (a, b) =>
        (rowsWhere n fun t => t.testBit u == a && t.testBit v == b, s u a b)
    | _ => []

/-- Rows `x_u ⊕ x_v = c`, `u < v` (`semxor`: c = 1; `semeq`: c = 0; `sem_pairs`). -/
def pairRows (n : Nat) (cs : List Bool) (s : Nat → Bool → Nat) : List (List Nat × Nat) :=
  (combs 2 (List.range n)).flatMap fun c =>
    match c with
    | [u, v] => cs.map fun c => (rowsWhere n fun t => (t.testBit u ^^ t.testBit v) == c, s u c)
    | _ => []

/-! ### The runs -/

/-- `best_opts` for a fully symmetric target: order, allin, first01, distinct. -/
def bestO : EOpts := { allin := true, first01 := true }

/-- `_restricted_size`: order, distinct. -/
def restrO : EOpts := {}

/-- `best_opts('w2_5_1')`: order, allin, distinct (not fully symmetric: no first01). -/
def w2bestO : EOpts := { allin := true }

/-- `cubes.base` at n = 5, r = 9: `best_opts` plus the table clause. -/
def cube5O : EOpts := { bestO with table := true }

/-- `ELIM=1` at n = 6, q = 1: `B_c = max(r − size(MOD3_5^{(1 − c) mod 3}), 0)`. -/
def elim6O : EOpts := { bestO with elim := some (c5 1, c5 0) }

/-- The r = 12 run's `redundancy` calls: `sem` (|S| = 1, 2), `semxor`, and `semeq` if `E`. -/
def red6 (E : Bool) : List (List Nat × Nat) :=
  sem1Rows 6 (fun _ c => c5 ((4 - c.toNat) % 3)) ++
  sem2Rows 6 (fun _ a b => c4 ((7 - a.toNat - b.toNat) % 3)) ++
  pairRows 6 [true] (fun _ _ => c4 0) ++
  (if E then pairRows 6 [false] (fun _ _ => 10) else [])

/-- `cubes.base` at n = 6, r = 12 with `ELIM=1 ELIM2=1 SEM=1,2 SEMXOR=1`, plus `SYMIN=1` if `S`
and `SEMEQ=1` if `E`: the ledgers `…_x`, `…_x_S`, `…_x_S_E`. -/
def full6O (S E : Bool) : EOpts :=
  { bestO with
    elim := some (c5 1, c5 0)
    elim2 := some (c4 1, c4 0, c4 2)
    red := red6 E
    symin := S
    table := true }

/-- `w2cubes.base`: `best_opts`, `symvars = (1, 2, 3, 4)`, `semrows = sem_general(|S| = 1, 2) +
sem_pairs`. -/
def w2cubeO : EOpts :=
  { w2bestO with
    symvars := some [1, 2, 3, 4]
    red := sem1Rows 5 sW1 ++ sem2Rows 5 sW2 ++ pairRows 5 [false, true] sWP }

/-- A run: inputs, truth table, options. -/
structure Run where
  n : Nat
  tt : Nat → Bool
  o : EOpts

def Run.cnf (R : Run) (r : Nat) : List (List Int) := cnfOf (events R.n r R.tt R.o)

/-- A cube's leaf: the base formula plus one unit clause per cube literal. -/
def Run.leafCnf (R : Run) (r : Nat) (cube : List L) : List (List Int) :=
  cnfOf (events R.n r R.tt R.o ++ cube.map fun l => .cl [l])

/-- The cube's unit clauses, numbered after the base (state `base`), on their own: the leaf's
CNF is the base's followed by these (`CnfRuns.leafCnf_split`). -/
def cubeCnf (base : NS) (cube : List L) : List (List Int) :=
  ((cube.map fun l => Ev.cl [l]).foldl NS.step { base with out := #[] }).out.toList

/-! ### Cubes (`cubes.all_cubes`, `w2cubes.all_cubes`) -/

/-- The first gate's table bits `(f01, f10, f11)` as a cube. -/
def tableCube (n : Nat) (b : Bool × Bool × Bool) : List L :=
  [(.fbit n false true, b.1), (.fbit n true false, b.2.1), (.fbit n true true, b.2.2)]

/-- `cubes_cover` with the table clause (`cubes.base`): every table but `0`, `x_j`, `x_k`, `(1,0,0)`. -/
def tables4 : List (Bool × Bool × Bool) :=
  [(false, false, true), (false, true, false), (true, true, false), (true, true, true)]

/-- `cubes_cover` without it (`w2cubes.base`). -/
def tables5 : List (Bool × Bool × Bool) :=
  [(false, false, true), (false, true, false), (true, false, false), (true, true, false), (true, true, true)]

/-- Gate `i`'s input pair `p` as a cube literal. -/
def pairLit (i : Nat) (p : Nat × Nat) : L := pos (.sel i p.1 p.2)

/-! ### The 22 runs -/

def best (n q : Nat) : Run := ⟨n, mod3T q n, bestO⟩
def cube5 (q : Nat) : Run := ⟨5, mod3T q 5, cube5O⟩
def restrW (n q : Nat) : Run := ⟨n, wqT q n, restrO⟩
def restrPq : Run := ⟨4, pqT, restrO⟩
def w2best : Run := ⟨5, wqT 1 5, w2bestO⟩
def w2cube : Run := ⟨5, wqT 1 5, w2cubeO⟩
def elim6 : Run := ⟨6, mod3T 1 6, elim6O⟩
/-- The r = 12 encodings by ledger: `0` = `…_x`, `1` = `…_x_S`, `2` = `…_x_S_E`. -/
def full6 (tag : Nat) : Run := ⟨6, mod3T 1 6, full6O (1 ≤ tag) (2 ≤ tag)⟩

/-! ### Leaves -/

/-- A cube of a split run: the ledger (`tag`, depth `split` in the tree) and index it is recorded
under. -/
structure Leaf where
  tag : Nat
  split : Nat
  idx : Nat
  cube : List L

/-- **`cubes.py`'s split tree.** Each level enumerates every value of one selector (the first
gate's table bits, then one gate's input pair), as cubes. A node at depth `d` with index `p` and
cube `c` is a leaf when `tagF d p` names its ledger; otherwise it splits into one child per
choice `i` of the next level, with index `p · #choices + i` and cube `c ++ choice`. Past the last
level every node is a leaf (ledger `dflt` unless `tagF` names one). -/
def tree (tagF : Nat → Nat → Option Nat) (dflt : Nat) :
    Nat → List (List (List L)) → Nat → List L → List Leaf
  | d, [], p, c => [⟨(tagF d p).getD dflt, d, p, c⟩]
  | d, lv :: rest, p, c =>
    match tagF d p with
    | some g => [⟨g, d, p, c⟩]
    | none => (List.range lv.length).flatMap fun i =>
        tree tagF dflt (d + 1) rest (p * lv.length + i) (c ++ lv.getD i [])

/-- The first gate's table, as a level. -/
def tableLevel (n : Nat) (ts : List (Bool × Bool × Bool)) : List (List L) := ts.map (tableCube n)

/-- Gate `i`'s input pair, as a level. -/
def pairLevel (i : Nat) : List (List L) := (pairs i).map fun p => [pairLit i p]

/-- `cubes.py` at n = 5, r = 9, `SPLIT=2`: table × gate 6's pair, index `15 ti + i1`. -/
def leaves5 : List Leaf := tree (fun _ _ => none) 0 0 [tableLevel 5 tables4, pairLevel 6] 0 []

/-- `w2cubes.py`, `SPLIT=1`: gate 5's pair × table, index `5 pi + ti` (depth 2 in the tree). -/
def leavesW2 : List Leaf := tree (fun _ _ => none) 0 0 [pairLevel 5, tableLevel 5 tables5] 0 []

/-- A ledger tag from the cover-tree data: `none` means split. -/
def tagAt (s : String) (i : Nat) : Option Nat :=
  match s.toList.getD i 's' with
  | 'a' => some 0
  | 'b' => some 1
  | 'c' => some 2
  | _ => none

/-- The r = 12 tree's data (`CnfLeaves`): at depth 3 (`SPLIT=3`, index `p`), 4 (`36 p + i3`)
and 5 (`45 q + i4`), which ledger certifies a cube, or (depths 3, 4) that it is split. -/
def tag12 (d p : Nat) : Option Nat :=
  if d = 3 then tagAt CnfLeaves.d3 p
  else if d = 4 then tagAt ((CnfLeaves.d4.lookup (p / 36)).getD "") (p % 36)
  else if d = 5 then tagAt ((CnfLeaves.d5.lookup (p / 45)).getD "") (p % 45)
  else none

/-- **The r = 12 leaves**: table × gates 7, 8 pairs, split where the data says by gate 9's pair
and then gate 10's. -/
def leaves12 : List Leaf :=
  tree tag12 2 0 [tableLevel 6 tables4, pairLevel 7, pairLevel 8, pairLevel 9, pairLevel 10] 0 []

/-! ### The 22 hypotheses, as one list (what `cnfexport` and `cnf_certify.py` iterate) -/

/-- A scan hypothesis: the run's CNF at every `r` from `lo` to `hi`. -/
structure ScanSpec where
  name : String
  run : Run
  lo : Nat
  hi : Nat

/-- A split-run hypothesis: every leaf's CNF at `r`. -/
structure SplitSpec where
  name : String
  run : Nat → Run
  r : Nat
  leaves : List Leaf

/-- The 17 scans of `CnfRuns.mod3_6_size_13`, in its order. -/
def scanList : List ScanSpec :=
  [⟨"best3_0", best 3 0, 1, 2⟩, ⟨"best3_1", best 3 1, 1, 3⟩, ⟨"best3_2", best 3 2, 1, 3⟩,
   ⟨"best4_0", best 4 0, 1, 6⟩, ⟨"best4_1", best 4 1, 1, 6⟩, ⟨"best4_2", best 4 2, 1, 5⟩,
   ⟨"best5_0", best 5 0, 1, 8⟩, ⟨"best5_1", best 5 1, 1, 8⟩, ⟨"best5_2", best 5 2, 1, 8⟩,
   ⟨"restr3_0", restrW 3 0, 1, 3⟩, ⟨"restr3_1", restrW 3 1, 1, 3⟩, ⟨"restr3_2", restrW 3 2, 1, 2⟩,
   ⟨"restr4_0", restrW 4 0, 1, 6⟩, ⟨"restr4_1", restrW 4 1, 1, 5⟩, ⟨"restr4_pq", restrPq, 1, 6⟩,
   ⟨"w2best", w2best, 1, 7⟩, ⟨"elim6", elim6, 1, 11⟩]

/-- The 5 split runs of `CnfRuns.mod3_6_size_13`, in its order. -/
def splitList : List SplitSpec :=
  [⟨"cube5_0", fun _ => cube5 0, 9, leaves5⟩, ⟨"cube5_2", fun _ => cube5 2, 9, leaves5⟩,
   ⟨"w2cube_8", fun _ => w2cube, 8, leavesW2⟩, ⟨"w2cube_9", fun _ => w2cube, 9, leavesW2⟩,
   ⟨"full6_12", full6, 12, leaves12⟩]

end CnfSpecs
