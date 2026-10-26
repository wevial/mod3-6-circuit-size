import Garden.CnfSpecs
import Garden.LratStream

/-!
# `lratdirect`: check an LRAT proof against a run's CNF built in memory

`lratcheck` reads a DIMACS file and a proof. Between a Lean-generated CNF and its verdict that
leaves `cnfexport`'s writer, `lratcheck`'s DIMACS parser, and (for the split runs) a sha256 link to
a ledger line. This file removes all three for any CNF it is pointed at: the executable
(`LratDirect.lean`) is given a run's name, `r` or a leaf index, and the proof file. It builds the
CNF that `CnfRuns.mod3_6_size_13`'s hypothesis names, `toCNF (R.cnf r)` or
`toCNF ((R L.tag).leafCnf r L.cube)`, looked up in `CnfSpecs.scanList`/`splitList`, and reads
nothing but the proof.

* `Job.cnf?`: the CNF a job names. `scan_cnf?`, `leaf_cnf?`: it is exactly the hypothesis's term.
* `check cnf blocks`: the proof's bytes, given as the blocks the executable read, parsed and fed
  through `LratStream.stepChunk` one block at a time. The executable's IO loop computes
  `finish (blocks.foldl feed (init cnf))` and nothing else.
* **`check_sound`**: if `check cnf blocks` is verified, `cnf.Unsat`. Whatever the parser does, the
  formula's history is `runChunks` over the chunks it produced (`run_fs`), so this is
  `LratStream.runChunks_sound`. The parser is not trusted: any action list that is accepted proves
  unsatisfiability.
* **`scan_sound`**, **`leaf_sound`**: the same for a job, concluding `Unsat` of the hypothesis's
  CNF. `DirectRuns.mod3_6_size_13_direct` composes them with `CnfRuns.mod3_6_size_13_lists`.

The proof may be CaDiCaL's binary LRAT (first byte `a` or `d`) or text LRAT (anything else). The
parser is strict, as `lratcheck`'s is: clause ids must be consecutive, literals in range, RAT and
zero hints are errors. Up to the verdict, a parse error in any block read, or a proof that ends
mid-action, rejects it. Reading stops at the verdict, so bytes in later blocks are never looked at,
and an incomplete action after the empty clause in the same block is ignored. An action longer than
a block is re-parsed from its start at each new block (quadratic in its length; CaDiCaL's are far
shorter than the 1 MiB blocks).

Trusted, not verified: the IO loop (read blocks in order until EOF or a verdict, then `finish`),
and the compiled code (the Lean compiler and runtime, `Std.HashMap`, core's compiled checker).
This file imports only `Std` and `Std`-only garden files, so `lratdirect` builds with the
toolchain alone (`research/lean/direct/`).
-/

namespace Garden.LratDirect
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open Garden.LratStream CnfGen CnfSpecs

/-! ## Which CNF -/

/-- What `lratdirect` is asked to check: a scan's CNF at `r`, or leaf `i` of a split run. -/
inductive Job where
  | scan (name : String) (r : Nat)
  | leaf (name : String) (i : Nat)

/-- The scan named `name` (names are distinct: `CnfRuns.names_nodup`). -/
def scanSpec? (name : String) : Option ScanSpec := scanList.find? (·.name == name)

/-- The split run named `name`. -/
def splitSpec? (name : String) : Option SplitSpec := splitList.find? (·.name == name)

/-- **The CNF a job names**, as DIMACS integers: the scan's CNF at `r` if `r` is in its range,
or the leaf's. `none` for an unknown name, an `r` outside the range, or no such leaf. -/
def Job.cnf? : Job → Option (List (List Int))
  | .scan name r =>
    match scanSpec? name with
    | some x => if x.lo ≤ r ∧ r ≤ x.hi then some (x.run.cnf r) else none
    | none => none
  | .leaf name i =>
    match splitSpec? name with
    | some x =>
      match x.leaves[i]? with
      | some L => some ((x.run L.tag).leafCnf x.r L.cube)
      | none => none
    | none => none

theorem scan_cnf? {name : String} {x : ScanSpec} {r : Nat} (h : scanSpec? name = some x)
    (hlo : x.lo ≤ r) (hhi : r ≤ x.hi) : (Job.scan name r).cnf? = some (x.run.cnf r) := by
  simp [Job.cnf?, h, hlo, hhi]

theorem leaf_cnf? {name : String} {x : SplitSpec} {i : Nat} {L : Leaf} (h : splitSpec? name = some x)
    (hL : x.leaves[i]? = some L) :
    (Job.leaf name i).cnf? = some ((x.run L.tag).leafCnf x.r L.cube) := by
  simp [Job.cnf?, h, hL]

theorem scanSpec?_mem {name : String} {x : ScanSpec} (h : scanSpec? name = some x) : x ∈ scanList :=
  List.mem_of_find?_eq_some h

theorem splitSpec?_mem {name : String} {x : SplitSpec} (h : splitSpec? name = some x) :
    x ∈ splitList :=
  List.mem_of_find?_eq_some h

/-! ## LRAT parsing (not trusted: any accepted action list proves `Unsat`) -/

/-- One step of the parser at position `i`. -/
inductive Step where
  | act (a : IntAction) (next : Nat)
  | skip (next : Nat)          -- a blank or comment line (text)
  | more                       -- the action is not complete in the buffer: wait for more bytes
  | err (msg : String)

/-- Binary: one varint at `i` (7 bits per byte, low first). -/
def readNum (buf : ByteArray) (i : Nat) (acc : Nat := 0) (shift : Nat := 0) : Option (Nat × Nat) :=
  if h : i < buf.size then
    let b := buf[i]
    let acc := acc ||| ((b &&& 127).toNat <<< shift)
    if b &&& 128 == 0 then some (acc, i + 1) else readNum buf (i + 1) acc (shift + 7)
  else none
termination_by buf.size - i

/-- Binary: signed numbers up to the terminating 0 (`2|x| + [x < 0]`). -/
def readList (buf : ByteArray) (i : Nat) (acc : Array Int := #[]) : Option (Array Int × Nat) :=
  match readNum buf i with
  | none => none
  | some (0, j) => some (acc, j)
  | some (u, j) =>
    if _h : i < j ∧ j ≤ buf.size then
      readList buf j (acc.push (if u &&& 1 == 1 then -((u >>> 1 : Nat) : Int) else ((u >>> 1 : Nat) : Int)))
    else none
termination_by buf.size - i

/-- An addition, checked the same way in both formats. -/
def addition (id nextId nVars : Nat) (lits hints : Array Int) (next : Nat) : Step :=
  if id ≠ nextId then .err s!"clause id {id}, expected {nextId}"
  else if lits.any (fun l => l.natAbs == 0 || l.natAbs > nVars) then
    .err s!"literal out of range in clause {id}"
  else if hints.any (· ≤ 0) then .err s!"RAT or zero hint in clause {id}"
  else
    let hs := hints.map Int.toNat
    if lits.isEmpty then .act (.addEmpty id hs) next else .act (.addRup id lits hs) next

def deletion (ids : Array Int) (next : Nat) : Step :=
  if ids.any (· ≤ 0) then .err "bad deletion id" else .act (.del (ids.map Int.toNat)) next

/-- Binary LRAT: `a id lits 0 hints 0` or `d ids 0`. -/
def binStep (buf : ByteArray) (i nextId nVars : Nat) : Step :=
  if h : i < buf.size then
    let tag := buf[i]
    if tag == 'a'.toUInt8 then
      match readNum buf (i + 1) with
      | none => .more
      | some (u, j) =>
        if u &&& 1 == 1 then .err "negative clause id" else
        match readList buf j with
        | none => .more
        | some (lits, j) =>
          match readList buf j with
          | none => .more
          | some (hints, j) => addition (u >>> 1) nextId nVars lits hints j
    else if tag == 'd'.toUInt8 then
      match readList buf (i + 1) with
      | none => .more
      | some (ids, j) => deletion ids j
    else .err s!"expected 'a' or 'd', got byte {tag}"
  else .more

/-- Text: the first `\n` at or after `i`. -/
def findNL (buf : ByteArray) (i : Nat) : Option Nat :=
  if h : i < buf.size then
    if buf[i] == 10 then some i else findNL buf (i + 1)
  else none
termination_by buf.size - i

def isSpace (b : UInt8) : Bool := b == 32 || b == 9 || b == 13

/-- Text: decimal digits from `j` (before `e`), and where they stop. -/
def digits (buf : ByteArray) (j e : Nat) (acc : Nat := 0) : Nat × Nat :=
  if h : j < e ∧ j < buf.size then
    let b := buf[j]
    if 48 ≤ b ∧ b ≤ 57 then digits buf (j + 1) e (acc * 10 + (b - 48).toNat) else (acc, j)
  else (acc, j)
termination_by e - j

/-- Text: the tokens of the line `buf[i:e]`; `d` is `none`, an integer `some k`. -/
def tokens (buf : ByteArray) (i e : Nat) (acc : Array (Option Int) := #[]) :
    Except String (Array (Option Int)) :=
  if h : i < e ∧ i < buf.size then
    let b := buf[i]
    if isSpace b then tokens buf (i + 1) e acc
    else
      let (tok, k) : Option Int × Nat :=
        if b == 'd'.toUInt8 then (none, i + 1)
        else
          let neg := b == '-'.toUInt8
          let j := if neg then i + 1 else i
          let (v, k) := digits buf j e
          (some (if neg then -(v : Int) else v), if k == j then i else k)
      if h2 : i < k then
        if k < e && (match buf[k]? with | some c => !isSpace c | none => false) then
          .error s!"bad token at byte {k}"
        else tokens buf k e (acc.push tok)
      else .error s!"bad token at byte {i}"
  else .ok acc
termination_by e - i

/-- Text LRAT: `id lits 0 hints 0` or `id d ids 0`, one per line; blank lines and lines starting
with `c` are skipped. -/
def textStep (buf : ByteArray) (i nextId nVars : Nat) : Step :=
  match findNL buf i with
  | none => .more
  | some e =>
    if buf[i]? == some 'c'.toUInt8 then .skip (e + 1) else
    match tokens buf i e with
    | .error m => .err m
    | .ok toks =>
      if toks.isEmpty then .skip (e + 1)
      else
        match toks[0]?, toks[1]? with
        | some (some id), some none =>                   -- `id d ids 0`
          let ids := toks.extract 2 toks.size
          if ids.all Option.isSome && ids.back? == some (some 0) then
            deletion ((ids.pop).map (·.getD 0)) (e + 1)
          else .err s!"bad deletion line after clause {id}"
        | some (some id), _ =>                           -- `id lits 0 hints 0`
          let rest := toks.extract 1 toks.size
          if !rest.all Option.isSome then .err s!"stray d in clause {id}" else
          let vs := rest.map (·.getD 0)
          match vs.findIdx? (· == 0) with
          | none => .err s!"clause {id} has no terminating 0"
          | some k =>
            let hints := vs.extract (k + 1) vs.size
            if hints.back? == some 0 then
              let hints := hints.pop
              if id < 0 then .err "negative clause id"
              else addition id.toNat nextId nVars (vs.extract 0 k) hints (e + 1)
            else .err s!"clause {id}: hints not terminated by 0"
        | _, _ => .err "line does not start with a clause id"

inductive Fmt where
  | binary
  | text
  deriving DecidableEq

def Fmt.name : Fmt → String
  | .binary => "binary"
  | .text => "text"

/-- Binary LRAT starts with an action tag; text LRAT with a clause id or a comment. -/
def detect (buf : ByteArray) : Option Fmt :=
  match buf[0]? with
  | none => none
  | some b => if b == 'a'.toUInt8 || b == 'd'.toUInt8 then some .binary else some .text

def step (fmt : Fmt) (buf : ByteArray) (i nextId nVars : Nat) : Step :=
  match fmt with
  | .binary => binStep buf i nextId nVars
  | .text => textStep buf i nextId nVars

/-- Every complete action from `i` on: the actions, where the incomplete rest starts, and the
next clause id. -/
def parseAll (fmt : Fmt) (buf : ByteArray) (i nextId nVars : Nat) (acc : Array IntAction := #[]) :
    Except String (Array IntAction × Nat × Nat) :=
  match step fmt buf i nextId nVars with
  | .more => .ok (acc, i, nextId)
  | .err m => .error s!"{m} (at clause id {nextId})"
  | .skip j =>
    if _h : i < j ∧ j ≤ buf.size then parseAll fmt buf j nextId nVars acc
    else .error "parser made no progress"
  | .act a j =>
    if _h : i < j ∧ j ≤ buf.size then
      let nextId := match a with | .del _ => nextId | _ => nextId + 1
      parseAll fmt buf j nextId nVars (acc.push a)
    else .error "parser made no progress"
termination_by buf.size - i

/-- The parser's state between blocks. -/
structure PS where
  fmt : Option Fmt := none     -- fixed by the first byte
  buf : ByteArray := .empty    -- bytes of an incomplete action
  nextId : Nat                 -- the id the next added clause must have
  nVars : Nat
  err : Option String := none
  count : Nat := 0             -- actions parsed

/-- Append a block; return the complete actions in it. On a parse error, none. -/
def PS.parse (ps : PS) (b : ByteArray) : PS × Array IntAction :=
  let buf := ps.buf ++ b
  match ps.fmt <|> detect buf with
  | none => ({ ps with buf }, #[])
  | some fmt =>
    match parseAll fmt buf 0 ps.nextId ps.nVars with
    | .ok (acts, j, nextId) =>
      ({ ps with fmt := some fmt, buf := buf.extract j buf.size, nextId, count := ps.count + acts.size },
       acts)
    | .error m => ({ ps with fmt := some fmt, buf := .empty, err := some m }, #[])

/-- End of file: a text proof's last line may lack its `\n`; anything left over is an error. -/
def PS.close (ps : PS) : PS × Array IntAction :=
  let (ps, acts) := if ps.fmt == some .text then ps.parse "\n".toUTF8 else (ps, #[])
  if ps.err.isNone && ps.buf.size > 0 then ({ ps with err := some "proof ends mid-action" }, #[])
  else (ps, acts)

/-! ## The checking function -/

/-- The formula so far, or the verdict. -/
abbrev FS (n : Nat) := Sum Result (DefaultFormula n)

/-- One chunk through `stepChunk`, as `runChunks` does it. -/
def advance {n : Nat} : FS n → Array IntAction → FS n
  | .inl r, _ => .inl r
  | .inr f, c => stepChunk f c 0

structure St (n : Nat) where
  fs : FS n
  ps : PS

/-- Before the first byte: the CNF converted as `check_sound` converts it, clause ids from
`#clauses + 1`, literals up to `numLiterals`. -/
def init (cnf : CNF Nat) : St (cnf.numLiterals + 1) :=
  ⟨.inr (CNF.convertLRAT cnf), { nextId := cnf.clauses.size + 1, nVars := cnf.numLiterals }⟩

/-- A verdict or a parse error: reading on would change nothing. -/
def St.stopped {n : Nat} (st : St n) : Bool := st.ps.err.isSome || st.fs.isLeft

/-- **One block of the proof.** -/
def feed {n : Nat} (st : St n) (b : ByteArray) : St n :=
  if st.stopped then st else
  match st with
  | ⟨fs, ps⟩ =>
    let (ps, c) := ps.parse b
    ⟨advance fs c, ps⟩

/-- **End of the proof.** -/
def finish {n : Nat} (st : St n) : St n :=
  if st.stopped then st else
  match st with
  | ⟨fs, ps⟩ =>
    let (ps, c) := ps.close
    ⟨advance fs c, ps⟩

structure Outcome where
  result : Result          -- core's verdict; `.outOfProof` if the proof ended without one
  err : Option String      -- a parse error
  fmt : Option Fmt
  actions : Nat

def Outcome.verified (o : Outcome) : Bool := o.err.isNone && o.result == .success

def St.outcome {n : Nat} (st : St n) : Outcome :=
  { result := match st.fs with | .inl r => r | .inr _ => .outOfProof
    err := st.ps.err, fmt := st.ps.fmt, actions := st.ps.count }

/-- What the executable computes from the blocks it read. -/
def run (cnf : CNF Nat) (blocks : List ByteArray) : St (cnf.numLiterals + 1) :=
  finish (blocks.foldl feed (init cnf))

/-- **The checking function.** -/
def check (cnf : CNF Nat) (blocks : List ByteArray) : Outcome := (run cnf blocks).outcome

/-- A job: its CNF (built here), against the proof's blocks. -/
def checkJob (j : Job) (blocks : List ByteArray) : Outcome :=
  match j.cnf? with
  | some F => check (toCNF F) blocks
  | none => { result := .outOfProof, err := some "no such run, r or leaf", fmt := none, actions := 0 }

/-! ## Soundness -/

theorem foldl_advance_inl {n : Nat} (r : Result) (cs : List (Array IntAction)) :
    cs.foldl advance (.inl r : FS n) = .inl r := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [List.foldl, advance] using ih

/-- If the chunks fed through `advance` end in `.success`, `runChunks` on them succeeds. -/
theorem runChunks_of_advance {n : Nat} (f : DefaultFormula n) (cs : List (Array IntAction))
    (h : cs.foldl advance (.inr f) = .inl .success) : runChunks f cs = .success := by
  induction cs generalizing f with
  | nil => simp at h
  | cons c cs ih =>
    simp only [List.foldl, advance] at h
    rw [runChunks]
    cases hs : stepChunk f c 0 with
    | inl r => rw [hs, foldl_advance_inl] at h; simpa using h
    | inr f' => rw [hs] at h; exact ih f' h

/-- Each block changes the formula by `advance` on some chunk (or not at all). -/
theorem feed_fs {n : Nat} (st : St n) (b : ByteArray) :
    ∃ cs : List (Array IntAction), (feed st b).fs = cs.foldl advance st.fs := by
  unfold feed
  split
  · exact ⟨[], rfl⟩
  · exact ⟨[(st.ps.parse b).2], rfl⟩

theorem finish_fs {n : Nat} (st : St n) :
    ∃ cs : List (Array IntAction), (finish st).fs = cs.foldl advance st.fs := by
  unfold finish
  split
  · exact ⟨[], rfl⟩
  · exact ⟨[st.ps.close.2], rfl⟩

theorem foldl_feed_fs {n : Nat} (st : St n) (bs : List ByteArray) :
    ∃ cs : List (Array IntAction), (bs.foldl feed st).fs = cs.foldl advance st.fs := by
  induction bs generalizing st with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
    obtain ⟨cs₁, h₁⟩ := feed_fs st b
    obtain ⟨cs₂, h₂⟩ := ih (feed st b)
    exact ⟨cs₁ ++ cs₂, by rw [List.foldl_cons, h₂, h₁, List.foldl_append]⟩

/-- **Whatever the parser produced, the formula's history is `advance` over some chunks.** -/
theorem run_fs (cnf : CNF Nat) (bs : List ByteArray) :
    ∃ cs : List (Array IntAction), (run cnf bs).fs = cs.foldl advance (.inr (CNF.convertLRAT cnf)) := by
  obtain ⟨cs₁, h₁⟩ := foldl_feed_fs (init cnf) bs
  obtain ⟨cs₂, h₂⟩ := finish_fs (bs.foldl feed (init cnf))
  exact ⟨cs₁ ++ cs₂, by rw [run, h₂, h₁, List.foldl_append]; rfl⟩

/-- **The result.** If the checking function accepts the proof's bytes, the CNF is unsatisfiable. -/
theorem check_sound (cnf : CNF Nat) (bs : List ByteArray) (h : (check cnf bs).verified = true) :
    cnf.Unsat := by
  obtain ⟨cs, hcs⟩ := run_fs cnf bs
  apply runChunks_sound cnf cs
  apply runChunks_of_advance
  rw [← hcs]
  simp only [check, St.outcome, Outcome.verified, Bool.and_eq_true, beq_iff_eq] at h
  revert h
  cases (run cnf bs).fs <;> simp

theorem checkJob_sound {j : Job} {F : List (List Int)} (hF : j.cnf? = some F) (bs : List ByteArray)
    (h : (checkJob j bs).verified = true) : (toCNF F).Unsat := by
  simp only [checkJob, hF] at h
  exact check_sound _ bs h

/-- **A scan**: if `lratdirect scan name r proof` is verified, the CNF the hypothesis
`ScanUnsat x.run x.lo x.hi` names at `r` is unsatisfiable. -/
theorem scan_sound {name : String} {x : ScanSpec} {r : Nat} (hx : scanSpec? name = some x)
    (hlo : x.lo ≤ r) (hhi : r ≤ x.hi) (bs : List ByteArray)
    (h : (checkJob (.scan name r) bs).verified = true) : (toCNF (x.run.cnf r)).Unsat :=
  checkJob_sound (scan_cnf? hx hlo hhi) bs h

/-- **A leaf**: if `lratdirect leaf name i proof` is verified, the CNF the hypothesis
`LeavesUnsat x.run x.r x.leaves` names for leaf `i` is unsatisfiable. -/
theorem leaf_sound {name : String} {x : SplitSpec} {i : Nat} {L : Leaf} (hx : splitSpec? name = some x)
    (hL : x.leaves[i]? = some L) (bs : List ByteArray)
    (h : (checkJob (.leaf name i) bs).verified = true) :
    (toCNF ((x.run L.tag).leafCnf x.r L.cube)).Unsat :=
  checkJob_sound (leaf_cnf? hx hL) bs h

end Garden.LratDirect
