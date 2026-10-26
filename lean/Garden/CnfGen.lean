import Std.Sat.CNF.Basic
import Std.Data.HashMap

/-!
# The SAT runs' CNFs, generated in Lean

A transcription of `research/circuits/optimal_circuit.encode` (with `sym = True`, one output, no
don't-cares, `maxfan = None`: every run here), of `cubes.base`'s table clause and of the cube
splits of `cubes.py` / `w2cubes.py`. It reproduces Python's variable numbering, clause order and
DIMACS writer, so a CNF generated here can be compared byte for byte with the one a ledger hashed.

It is written in two layers, so that what the clauses *say* and how they are *numbered* are
separate questions:

* **Symbolic.** Each variable has a meaning `M` (`sel i j k`: gate `i` reads nodes `j < k`;
  `val i t`: node `i`'s value on row `t`; `red T g`: gate `g` is redundant on the rows `T`; …).
  `events n r tt o` is the run's clause list over meanings, in Python's order, interleaved with
  `decl m` events at exactly the points where Python calls `new()`. Python's lazily created
  `diff`/`same` variables are `lazy m defs` events: declare `m` and emit `defs` unless `m` exists.
* **Numbering.** `number` folds over the events with a hash map from meanings to variables, so
  the `k`-th declared meaning is variable `k`, as Python's counter makes it. `cnfOf` is the
  numbered clause list and `dimacs` writes it the way `lrat.write_dimacs` does.

This file imports only `Std`, so the exporter (`CnfExport.lean`, exe `cnfexport`) does not link
Mathlib. What the clauses mean for a circuit is proved in `CnfSound.lean`; the runs are in
`CnfRuns.lean`.
-/

namespace CnfGen

/-- What a CNF variable means (one constructor per kind of Python variable). -/
inductive M where
  | sel (i j k : Nat)
  | fbit (i : Nat) (p q : Bool)
  | val (i t : Nat)
  | osel (i : Nat)
  | neg
  | dd (i i2 t : Nat)
  | kv (v g : Nat) (c : Bool)
  | e1 (v : Nat) (c : Bool) (h : Nat)
  | e2 (u v : Nat) (a b : Bool) (h : Nat)
  | red (T : List Nat) (g : Nat)
  | diff (h g t : Nat)
  | same (h g t : Nat)
  deriving DecidableEq, Hashable, Repr

/-- A literal over meanings: `(m, true)` is the variable, `(m, false)` its negation. -/
abbrev L := M × Bool

@[inline] def pos (m : M) : L := (m, true)
@[inline] def ng (m : M) : L := (m, false)

/-- One step of the generator. -/
inductive Ev where
  | decl (m : M)
  | cl (c : List L)
  | lazy (m : M) (defs : List (List L))

/-! ### Python's iteration orders -/

/-- `itertools.combinations(xs, k)`. -/
def combs {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combs k xs).map (x :: ·) ++ combs (k + 1) xs

/-- `itertools.combinations(range(i), 2)` as pairs. -/
def pairs (i : Nat) : List (Nat × Nat) :=
  (List.range i).flatMap fun j => ((List.range i).filter (j < ·)).map (j, ·)

/-- `gates = range(n, n + r)`. -/
def gates (n r : Nat) : List Nat := List.range' n r

/-- `sel.items()`: keys `(i, j, k)` in insertion order. -/
def selItems (n r : Nat) : List (Nat × Nat × Nat) :=
  (gates n r).flatMap fun i => (pairs i).map fun p => (i, p.1, p.2)

def rows (n : Nat) : List Nat := List.range (2 ^ n)

/-- `exactly_one(lits)`: the clause, then `[-a, -b]` for every pair. -/
def exactlyOne (ms : List M) : List Ev :=
  .cl (ms.map pos) :: (combs 2 ms).map fun c => .cl (c.map ng)

/-- `[-e[h] for h in cc]` for every `(k)`-subset `cc` of the gates: at most `k − 1` are true. -/
def atMost (n r k : Nat) (e : Nat → M) : List Ev :=
  (combs k (gates n r)).map fun cc => .cl (cc.map fun h => ng (e h))

/-! ### The encoding (`encode`'s main loop) -/

/-- `lit_val(node, t, b)`: `True`/`False` for an input, else `±val[node, t]`. -/
inductive LV where
  | tru
  | fls
  | lit (l : L)
  deriving DecidableEq

def litVal (n j t : Nat) (p : Bool) : LV :=
  if j < n then (if t.testBit j == p then .tru else .fls) else .lit (.val j t, p)

def LV.negs : LV → List L
  | .lit (m, b) => [(m, !b)]
  | _ => []

/-- The value clauses of gate `i` reading `(j, k)`, on row `t`, for `x_j = p`, `x_k = q`. -/
def valBlock (n i j k t : Nat) (p q : Bool) : List Ev :=
  let a := litVal n j t p
  let b := litVal n k t q
  if a = .fls ∨ b = .fls then [] else
    let prem := ng (.sel i j k) :: (a.negs ++ b.negs)
    if p = false ∧ q = false then [.cl (prem ++ [ng (.val i t)])]
    else [.cl (prem ++ [ng (.val i t), pos (.fbit i p q)]),
          .cl (prem ++ [pos (.val i t), ng (.fbit i p q)])]

/-- `for p in (0, 1): for q in (0, 1)`. -/
def valCls (n i j k t : Nat) : List Ev :=
  valBlock n i j k t false false ++ valBlock n i j k t false true ++
  valBlock n i j k t true false ++ valBlock n i j k t true true

/-- Every `new()` before the first clause: per gate `sel`, `fbit`, `val`; then `outsel`, `neg`. -/
def coreDecls (n r : Nat) : List Ev :=
  ((gates n r).flatMap fun i =>
    (pairs i).map (fun p => .decl (.sel i p.1 p.2)) ++
    [.decl (.fbit i false true), .decl (.fbit i true false), .decl (.fbit i true true)] ++
    (rows n).map fun t => .decl (.val i t)) ++
  (gates n r).map (fun i => .decl (.osel i)) ++ [.decl .neg]

def coreCls (n r : Nat) : List Ev :=
  (gates n r).flatMap fun i =>
    exactlyOne ((pairs i).map fun p => .sel i p.1 p.2) ++
    (pairs i).flatMap fun p => (rows n).flatMap fun t => valCls n i p.1 p.2 t

/-- `sym`: no degenerate table; every gate is the output or read later. -/
def symCls (n r : Nat) : List Ev :=
  (gates n r).flatMap fun i =>
    [.cl [pos (.fbit i false true), pos (.fbit i true false), pos (.fbit i true true)],
     .cl [pos (.fbit i false true), ng (.fbit i true false), ng (.fbit i true true)],
     .cl [ng (.fbit i false true), pos (.fbit i true false), ng (.fbit i true true)],
     .cl (pos (.osel i) :: ((selItems n r).filter fun x => i < x.1 ∧ (x.2.1 = i ∨ x.2.2 = i)).map
        fun x => pos (.sel x.1 x.2.1 x.2.2))]

/-- Python's tuple comparison `b < a`. -/
def pairLt (b a : Nat × Nat) : Bool := b.1 < a.1 || (b.1 == a.1 && b.2 < a.2)

def orderCls (n r : Nat) : List Ev :=
  (gates n (r - 1)).flatMap fun i =>
    (pairs i).flatMap fun a =>
      ((pairs (i + 1)).filter fun b => b.1 ≠ i ∧ b.2 ≠ i).filterMap fun b =>
        if pairLt b a then some (.cl [ng (.sel i a.1 a.2), ng (.sel (i + 1) b.1 b.2)]) else none

/-- `essential_inputs`. -/
def essential (n : Nat) (tt : Nat → Bool) : List Nat :=
  (List.range n).filter fun v => (rows n).any fun t => tt t != tt (t ^^^ (1 <<< v))

def allinCls (n r : Nat) (tt : Nat → Bool) : List Ev :=
  (essential n tt).map fun v =>
    .cl (((selItems n r).filter fun x => x.2.1 = v ∨ x.2.2 = v).map fun x => pos (.sel x.1 x.2.1 x.2.2))

/-- `g(t)` for the trivial functions `0, x_0, …, x_{n−1}` (`none` is `0`). -/
def trivVal (g : Option Nat) (t : Nat) : Bool :=
  match g with
  | none => false
  | some v => t.testBit v

def distinctCls (n r : Nat) : List Ev :=
  ((gates n r).flatMap fun i =>
    (none :: (List.range n).map some).flatMap fun g =>
      [.cl ((rows n).map fun t => if !trivVal g t then pos (.val i t) else ng (.val i t)),
       .cl ((rows n).map fun t => if !trivVal g t then ng (.val i t) else pos (.val i t))]) ++
  ((combs 2 (gates n r)).flatMap fun c =>
    match c with
    | [i, i2] =>
      ((rows n).map fun t => .decl (.dd i i2 t)) ++
      ((rows n).flatMap fun t =>
        [.cl [ng (.dd i i2 t), pos (.val i t), pos (.val i2 t)],
         .cl [ng (.dd i i2 t), ng (.val i t), ng (.val i2 t)],
         .cl [pos (.dd i i2 t), ng (.val i t), pos (.val i2 t)],
         .cl [pos (.dd i i2 t), pos (.val i t), ng (.val i2 t)]]) ++
      [.cl ((rows n).map fun t => pos (.dd i i2 t)), .cl ((rows n).map fun t => ng (.dd i i2 t))]
    | _ => [])

/-! ### `elim`, `elim2` -/

def kCls (n r v : Nat) : List Ev :=
  ((gates n r).flatMap fun g => [.decl (.kv v g false), .decl (.kv v g true)]) ++
  (selItems n r).flatMap fun x =>
    let g := x.1; let j := x.2.1; let k := x.2.2
    let s := M.sel g j k
    (if j = v then
      [.cl [ng s, pos (.fbit g false true), pos (.kv v g false)],
       .cl [ng s, ng (.fbit g true false), ng (.fbit g true true), pos (.kv v g true)],
       .cl [ng s, pos (.fbit g true false), pos (.fbit g true true), pos (.kv v g true)]] else []) ++
    (if k = v then
      [.cl [ng s, pos (.fbit g true false), pos (.kv v g false)],
       .cl [ng s, ng (.fbit g false true), ng (.fbit g true true), pos (.kv v g true)],
       .cl [ng s, pos (.fbit g false true), pos (.fbit g true true), pos (.kv v g true)]] else [])

def e1Cls (n r v : Nat) (c : Bool) (B : Nat) : List Ev :=
  ((gates n r).map fun h => .decl (.e1 v c h)) ++
  ((selItems n r).flatMap fun x =>
    let h := x.1; let j := x.2.1; let k := x.2.2
    (if j = v ∨ k = v then [.cl [ng (.sel h j k), pos (.e1 v c h)]] else []) ++
    ([j, k].filter (n ≤ ·)).map fun g => .cl [ng (.sel h j k), ng (.kv v g c), pos (.e1 v c h)]) ++
  atMost n r (B + 1) (.e1 v c)

/-- `elim = (B_0, B_1)`, given as the sizes `s_c` with `B_c = max(r − s_c, 0)`. -/
def elimCls (n r : Nat) (s : Nat × Nat) : List Ev :=
  (List.range n).flatMap fun v => kCls n r v ++ e1Cls n r v false (r - s.1) ++ e1Cls n r v true (r - s.2)

def e2Cls (n r u v : Nat) (a b : Bool) (B : Nat) : List Ev :=
  ((gates n r).map fun h => .decl (.e2 u v a b h)) ++
  ((selItems n r).flatMap fun x =>
    let h := x.1; let j := x.2.1; let k := x.2.2
    (if (j = u ∨ k = u) ∨ (j = v ∨ k = v) then [.cl [ng (.sel h j k), pos (.e2 u v a b h)]] else []) ++
    ([j, k].filter (n ≤ ·)).flatMap fun g =>
      [.cl [ng (.sel h j k), ng (.kv u g a), pos (.e2 u v a b h)],
       .cl [ng (.sel h j k), ng (.kv v g b), pos (.e2 u v a b h)],
       .cl [ng (.sel h j k), ng (.sel g u v), pos (.e2 u v a b h)]]) ++
  atMost n r (B + 1) (.e2 u v a b)

/-- `elim2 = (B_0, B_1, B_2)`, as sizes: `B_{a+b} = max(r − s_{a+b}, 0)`. -/
def elim2Cls (n r : Nat) (s : Nat × Nat × Nat) : List Ev :=
  (combs 2 (List.range n)).flatMap fun c =>
    match c with
    | [u, v] =>
      [(false, false), (false, true), (true, false), (true, true)].flatMap fun (a, b) =>
        e2Cls n r u v a b (r - [s.1, s.2.1, s.2.2].getD (a.toNat + b.toNat) 0)
    | _ => []

/-! ### `redundancy(T, B)`, with `B = r − s` -/

/-- `dlit(h, g, t, True)` / `(…, False)`: the lazily created `diff`/`same` variable. -/
def diffEv (h g t : Nat) : Ev :=
  .lazy (.diff h g t) [[ng (.diff h g t), pos (.val h t), pos (.val g t)],
    [ng (.diff h g t), ng (.val h t), ng (.val g t)]]

def sameEv (h g t : Nat) : Ev :=
  .lazy (.same h g t) [[ng (.same h g t), pos (.val h t), ng (.val g t)],
    [ng (.same h g t), ng (.val h t), pos (.val g t)]]

def redCls (n r : Nat) (T : List Nat) (s : Nat) : List Ev :=
  if s = 0 then [] else    -- `if B >= r: return`
  ((gates n r).map fun g => .decl (.red T g)) ++
  ((gates n r).flatMap fun g =>
    [.cl ((T.map fun t => pos (.val g t)) ++ [pos (.red T g)]),
     .cl ((T.map fun t => ng (.val g t)) ++ [pos (.red T g)])] ++
    ((List.range n).flatMap fun u =>
      [.cl ((T.map fun t => if t.testBit u then ng (.val g t) else pos (.val g t)) ++ [pos (.red T g)]),
       .cl ((T.map fun t => if t.testBit u then pos (.val g t) else ng (.val g t)) ++ [pos (.red T g)])]) ++
    ((gates n r).filter (· < g)).flatMap fun h =>
      (T.map fun t => diffEv h g t) ++ [.cl ((T.map fun t => pos (.diff h g t)) ++ [pos (.red T g)])] ++
      (T.map fun t => sameEv h g t) ++ [.cl ((T.map fun t => pos (.same h g t)) ++ [pos (.red T g)])]) ++
  atMost n r (r - s + 1) (.red T)

/-! ### `first01`, `symin`, `symvars`, the outputs, and `cubes.base`'s table clause -/

/-- `symin`/`symvars`' chain clause: a gate reading `x_w` implies one at or before it reads `x_u`. -/
def chainCls (n r u w : Nat) : List Ev :=
  ((selItems n r).filter fun x => x.2.1 = w ∨ x.2.2 = w).map fun x =>
    .cl (ng (.sel x.1 x.2.1 x.2.2) ::
      ((selItems n r).filter fun y => y.1 ≤ x.1 ∧ (y.2.1 = u ∨ y.2.2 = u)).map
        fun y => pos (.sel y.1 y.2.1 y.2.2))

def syminCls (n r : Nat) : List Ev := (List.range (n - 1)).flatMap fun u => chainCls n r u (u + 1)

def tableCl (n a b : Nat) : Ev :=
  .cl [ng (.sel n a b), ng (.fbit n false true), pos (.fbit n true false), pos (.fbit n true true)]

def symvarsCls (n r : Nat) (S : List Nat) : List Ev :=
  ((S.zip S.tail).flatMap fun p => chainCls n r p.1 p.2) ++
  (combs 2 S).flatMap fun c =>
    match c with
    | [a, b] => [tableCl n a b]
    | _ => []

def outCls (n r : Nat) (tt : Nat → Bool) : List Ev :=
  exactlyOne ((gates n r).map .osel) ++
  (gates n r).flatMap fun i => (rows n).flatMap fun t =>
    if tt t then [.cl [ng (.osel i), pos (.val i t), pos .neg], .cl [ng (.osel i), ng (.val i t), ng .neg]]
    else [.cl [ng (.osel i), pos (.val i t), ng .neg], .cl [ng (.osel i), ng (.val i t), pos .neg]]

/-- `cubes.base`: the first gate's table is not `(1, 0, 0)`. -/
def firstTableCl (n : Nat) : Ev :=
  .cl [ng (.fbit n false true), pos (.fbit n true false), pos (.fbit n true true)]

/-! ### A run's options, and its CNF -/

/-- `encode`'s keyword arguments (with `sym = True`), plus `cubes.base`'s clause (`table`).
Bounds are stored as the sizes they subtract (`B = r − s`), so they do not depend on `r`;
`red` lists `encode`'s `redundancy` calls in order (`sem`, `semxor`, `semrows`, `semeq`). -/
structure EOpts where
  order : Bool := true
  allin : Bool := false
  first01 : Bool := false
  distinct : Bool := true
  elim : Option (Nat × Nat) := none
  elim2 : Option (Nat × Nat × Nat) := none
  red : List (List Nat × Nat) := []
  symin : Bool := false
  symvars : Option (List Nat) := none
  table : Bool := false

/-- **`encode(n, [tt], r, True, **opts)`**, as events. -/
def events (n r : Nat) (tt : Nat → Bool) (o : EOpts) : List Ev :=
  coreDecls n r ++ coreCls n r ++ symCls n r ++
  (if o.order then orderCls n r else []) ++
  (if o.allin then allinCls n r tt else []) ++
  (if o.distinct then distinctCls n r else []) ++
  (match o.elim with | some s => elimCls n r s | none => []) ++
  (match o.elim2 with | some s => elim2Cls n r s | none => []) ++
  (o.red.flatMap fun x => redCls n r x.1 x.2) ++
  (if o.first01 then [.cl [pos (.sel n 0 1)]] else []) ++
  (if o.symin then syminCls n r else []) ++
  (match o.symvars with | some S => symvarsCls n r S | none => []) ++
  outCls n r tt ++
  (if o.table then [firstTableCl n] else [])

/-! ### Numbering -/

structure NS where
  map : Std.HashMap M Nat := {}
  /-- `decls[k]` is the meaning of DIMACS variable `k + 1`. -/
  decls : Array M := #[]
  out : Array (List Int) := #[]

def NS.declare (s : NS) (m : M) : NS :=
  { s with map := s.map.insert m (s.decls.size + 1), decls := s.decls.push m }

/-- Variable `k`, or its negation. -/
def mkLit (k : Nat) (b : Bool) : Int := if b then (k : Int) else -(k : Int)

def NS.lit (s : NS) (l : L) : NS × Int :=
  match s.map[l.1]? with
  | some k => (s, mkLit k l.2)
  | none => (s.declare l.1, mkLit (s.decls.size + 1) l.2)

def NS.lits : NS → List L → NS × List Int
  | s, [] => (s, [])
  | s, l :: ls =>
    let (s1, i) := s.lit l
    let (s2, is) := s1.lits ls
    (s2, i :: is)

def NS.clause (s : NS) (c : List L) : NS :=
  let (s1, is) := s.lits c
  { s1 with out := s1.out.push is }

def NS.step (s : NS) : Ev → NS
  | .decl m => s.declare m
  | .cl c => s.clause c
  | .lazy m defs => if s.map.contains m then s else defs.foldl NS.clause (s.declare m)

def number (evs : List Ev) : NS := evs.foldl NS.step {}

/-- The numbered clauses, as DIMACS integers. -/
def cnfOf (evs : List Ev) : List (List Int) := (number evs).out.toList

/-! ### The CNF type of `lratcheck`'s verified checker, and the DIMACS writer -/

/-- A DIMACS literal as `LratCheck.parseDimacs` reads it. -/
def litOf (l : Int) : Std.Sat.Literal Nat := (l.natAbs - 1, decide (0 < l))

def toCNF (F : List (List Int)) : Std.Sat.CNF Nat := ⟨(F.map fun c => c.map litOf).toArray⟩

/-- `' '.join(map(str, c)) + ' 0\n'`. -/
def clauseLine (c : List Int) : String := " ".intercalate (c.map toString) ++ " 0\n"

/-- `max(abs(l) for c in cnf for l in c)`, 0 if none. -/
def maxVar (F : List (List Int)) : Nat := F.foldl (fun m c => c.foldl (fun m l => max m l.natAbs) m) 0

def header (nv m : Nat) : String := "p cnf " ++ toString nv ++ " " ++ toString m ++ "\n"

def body (F : List (List Int)) : String := String.join (F.map clauseLine)

/-- **`lrat.write_dimacs`.** -/
def dimacs (F : List (List Int)) : String := header (maxVar F) F.length ++ body F

end CnfGen
