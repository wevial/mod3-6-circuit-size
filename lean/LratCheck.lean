import Garden.LratStream
import Std.Sync.Channel

/-!
# `lratcheck`: stream a binary LRAT proof through Lean's verified checker

    lratcheck <formula.cnf> <proof.lrat | FIFO>      -- exit 0 and "s VERIFIED UNSAT" on acceptance
    lratcheck --dump-cnf <formula.cnf>               -- print the parsed CNF back as DIMACS

The proof is CaDiCaL's binary LRAT (`--lrat=true --binary=true`). It is read in 4 MB blocks
and cut into chunks of 100k actions; the chunks go through `Garden.LratStream.stepChunk` in the
shape of `runChunks`, whose acceptance implies `CNF.Unsat` of the parsed formula
(`runChunks_sound`, checked by Lean).

Trusted, not verified: the DIMACS parser (hence `--dump-cnf`, for a diff against the input) and
this IO loop matching `runChunks` (empty chunk = end of the list). Not trusted: the LRAT parser.
Whatever actions it produces, acceptance still means unsatisfiable. It is strict anyway: clause
ids must be consecutive (core's checker ignores them and appends), literals must be in range,
RAT hints and trailing garbage are errors, so a malformed proof fails loudly, not silently.
-/

open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open Garden.LratStream

/-! ## DIMACS -/

def parseDimacs (s : String) : Except String (CNF Nat) := do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : Array (Literal Nat) := #[]
  let mut declared : Option (Nat × Nat) := none
  for line in s.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then continue
    if line.startsWith "p" then
      match (line.splitOn " ").filter (· ≠ "") with
      | ["p", "cnf", v, c] =>
        match v.toNat?, c.toNat? with
        | some v, some c => declared := some (v, c)
        | _, _ => throw s!"bad header: {line}"
      | _ => throw s!"bad header: {line}"
      continue
    for tok in (line.splitOn " ").filter (· ≠ "") do
      match tok.toInt? with
      | none => throw s!"bad token: {tok}"
      | some 0 =>
        clauses := clauses.push cur.toList
        cur := #[]
      | some k =>
        if let some (v, _) := declared then
          if k.natAbs > v then throw s!"literal {k} beyond declared {v} variables"
        cur := cur.push (k.natAbs - 1, decide (k > 0))
  if !cur.isEmpty then throw "last clause not terminated by 0"
  match declared with
  | none => throw "no p cnf header"
  | some (_, c) =>
    if c ≠ clauses.size then throw s!"header says {c} clauses, found {clauses.size}"
  return ⟨clauses⟩

def dumpDimacs (cnf : CNF Nat) : String := Id.run do
  let nv := match cnf.maxLiteral with | none => 0 | some m => m + 1
  let mut out := s!"p cnf {nv} {cnf.clauses.size}\n"
  for c in cnf.clauses do
    for (v, b) in c do
      out := out ++ (if b then s!"{v + 1} " else s!"-{v + 1} ")
    out := out ++ "0\n"
  return out

/-! ## Binary LRAT, streamed -/

/-- Result of trying to parse one action from a buffer. -/
inductive PR where
  | ok (a : IntAction) (next : Nat)
  | more                     -- ran off the end of the buffer: refill and retry
  | err (msg : String)

/-- One varint at `i` (7 bits per byte, low first). -/
partial def readNum (buf : ByteArray) (i : Nat) (acc : Nat := 0) (shift : Nat := 0) :
    Option (Nat × Nat) :=
  if h : i < buf.size then
    let b := buf[i]
    let acc := acc ||| ((b &&& 127).toNat <<< shift)
    if b &&& 128 == 0 then some (acc, i + 1) else readNum buf (i + 1) acc (shift + 7)
  else none

/-- Signed numbers up to the terminating 0 (encoding: `2|x| + [x < 0]`). -/
partial def readList (buf : ByteArray) (i : Nat) (acc : Array Int := #[]) :
    Option (Array Int × Nat) :=
  match readNum buf i with
  | none => none
  | some (0, j) => some (acc, j)
  | some (u, j) =>
    let x : Int := if u &&& 1 == 1 then -((u >>> 1 : Nat) : Int) else ((u >>> 1 : Nat) : Int)
    readList buf j (acc.push x)

def parseAction (buf : ByteArray) (i : Nat) (nextId : Nat) (nVars : Nat) : PR :=
  if h : i < buf.size then
    let tag := buf[i]
    if tag == 'a'.toUInt8 then
      match readNum buf (i + 1) with
      | none => .more
      | some (u, j) =>
        if u &&& 1 == 1 then .err "negative clause id" else
        let id := u >>> 1
        if id ≠ nextId then .err s!"clause id {id}, expected {nextId}" else
        match readList buf j with
        | none => .more
        | some (lits, j) =>
          match readList buf j with
          | none => .more
          | some (hints, j) =>
            if lits.any (fun l => l.natAbs == 0 || l.natAbs > nVars) then
              .err s!"literal out of range in clause {id}"
            else if hints.any (· ≤ 0) then .err s!"RAT or zero hint in clause {id}"
            else
              let hs := hints.map Int.toNat
              if lits.isEmpty then .ok (.addEmpty id hs) j else .ok (.addRup id lits hs) j
    else if tag == 'd'.toUInt8 then
      match readList buf (i + 1) with
      | none => .more
      | some (ids, j) =>
        if ids.any (· ≤ 0) then .err "bad deletion id" else .ok (.del (ids.map Int.toNat)) j
    else .err s!"expected 'a' or 'd', got byte {tag}"
  else .more

structure Reader where
  ch : Std.CloseableChannel.Sync ByteArray   -- blocks from the reader thread; closed at EOF
  buf : ByteArray
  pos : Nat
  eof : Bool
  nextId : Nat
  nVars : Nat

def blockSize : USize := 1024 * 1024

/-- Reader thread. `Handle.read` is a blocking `fread`; done inline, it serialises the solver
(stalled on a full pipe) and the checker (stalled on `fread`). A thread that only reads keeps
the pipe drained, so the two run side by side (measured 2026-09-28: 11.9 s in series, see log). -/
partial def pump (h : IO.FS.Handle) (ch : Std.CloseableChannel.Sync ByteArray) : IO Unit := do
  let b ← h.read blockSize
  if b.isEmpty then
    ch.close
  else
    ch.send b
    pump h ch

/-- Up to `k` actions. An empty result means the proof ended cleanly. -/
partial def Reader.chunk (r : Reader) (k : Nat) (acc : Array IntAction := #[]) :
    IO (Array IntAction × Reader) := do
  if acc.size ≥ k then return (acc, r)
  match parseAction r.buf r.pos r.nextId r.nVars with
  | .ok a j =>
    let nextId := match a with | .addEmpty .. | .addRup .. | .addRat .. => r.nextId + 1 | .del _ => r.nextId
    Reader.chunk { r with pos := j, nextId } k (acc.push a)
  | .err m => throw (IO.userError s!"proof parse error after {r.nextId - 1}: {m}")
  | .more =>
    if r.eof then
      if r.pos < r.buf.size then throw (IO.userError "proof truncated mid-action")
      return (acc, r)
    match ← r.ch.recv with
    | none => Reader.chunk { r with eof := true } k acc
    | some more =>
      let buf := r.buf.extract r.pos r.buf.size ++ more
      Reader.chunk { r with buf, pos := 0 } k acc

/-- The IO shape of `runChunks`. -/
partial def loop {n : Nat} (f : DefaultFormula n) (r : Reader) (count : Nat) :
    IO (Result × Nat) := do
  let (c, r) ← r.chunk 100000
  if c.isEmpty then return (.outOfProof, count)
  match stepChunk f c 0 with
  | .inl res => return (res, count + c.size)
  | .inr f' => loop f' r (count + c.size)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump-cnf", cnfPath] =>
    match parseDimacs (← IO.FS.readFile cnfPath) with
    | .error e => IO.eprintln e; return 2
    | .ok cnf => IO.print (dumpDimacs cnf); return 0
  | [cnfPath, proofPath] =>
    let t0 ← IO.monoMsNow
    let cnf ← match parseDimacs (← IO.FS.readFile cnfPath) with
      | .error e => IO.eprintln s!"s NOT VERIFIED (cnf: {e})"; return 1
      | .ok c => pure c
    let f := CNF.convertLRAT cnf
    let h ← IO.FS.Handle.mk proofPath .read
    let ch ← Std.CloseableChannel.Sync.new (some 256)   -- at most 256 MB buffered
    let _ ← IO.asTask (prio := .dedicated) (pump h ch)
    let r : Reader := ⟨ch, .empty, 0, false, cnf.clauses.size + 1, cnf.numLiterals⟩
    try
      let (res, count) ← loop f r 0
      let dt := (← IO.monoMsNow) - t0
      if res == .success then
        IO.println s!"s VERIFIED UNSAT ({count} actions, {dt} ms)"; return 0
      else
        IO.println s!"s NOT VERIFIED ({match res with | .success => "success" | .outOfProof => "outOfProof" | .rupFailure => "rupFailure"} after {count} actions, {dt} ms)"; return 1
    catch e =>
      IO.println s!"s NOT VERIFIED ({e})"; return 1
  | _ => IO.eprintln "usage: lratcheck <cnf> <binary-lrat> | lratcheck --dump-cnf <cnf>"; return 2
