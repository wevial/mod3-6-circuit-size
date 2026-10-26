import Garden.LratDirect

/-!
# `lratdirect`: check an LRAT proof against a run's CNF, built in memory

    lratdirect scan <run> <r> <proof>     -- `toCNF (R.cnf r)` for the scan named <run>
    lratdirect leaf <run> <i> <proof>     -- `toCNF ((R L.tag).leafCnf r L.cube)` for leaf i

Names, ranges and leaf indices are `CnfSpecs.scanList`/`splitList`'s (`cnfexport list` prints
them). The proof is CaDiCaL's LRAT, binary or text. Prints `s VERIFIED UNSAT …` and exits 0 iff
`Garden.LratDirect.check` accepts, which implies the CNF is unsatisfiable (`check_sound`,
`scan_sound`, `leaf_sound`); otherwise `s NOT VERIFIED …` and exit 1; exit 2 for a bad job.

Trusted, not verified: this loop. It reads the file in blocks, in order, feeds each to `feed`
until EOF or until the state is `stopped` (a verdict or a parse error, after which `feed` is the
identity), then applies `finish`. That is `run cnf blocks` for the blocks read.
-/

open Garden.LratDirect CnfGen

def blockSize : USize := 1024 * 1024

partial def readLoop {n : Nat} (h : IO.FS.Handle) (st : St n) : IO (St n) := do
  if st.stopped then return st
  let b ← h.read blockSize
  if b.isEmpty then return st
  readLoop h (feed st b)

def resultName : Std.Tactic.BVDecide.LRAT.Internal.Result → String
  | .success => "success"
  | .outOfProof => "outOfProof"
  | .rupFailure => "rupFailure"

def main (args : List String) : IO UInt32 := do
  let job? : Option (Job × String × String) := match args with
    | ["scan", name, r, p] => r.toNat?.map fun k => (.scan name k, s!"scan {name} r={k}", p)
    | ["leaf", name, i, p] => i.toNat?.map fun k => (.leaf name k, s!"leaf {name} {k}", p)
    | _ => none
  let some (j, label, path) := job?
    | IO.eprintln "usage: lratdirect scan <run> <r> <proof> | lratdirect leaf <run> <i> <proof>"; return 2
  let some F := j.cnf?
    | IO.eprintln s!"{label}: no such run, r outside its range, or no such leaf (see `cnfexport list`)"; return 2
  let t0 ← IO.monoMsNow
  let cnf := toCNF F
  let st0 := init cnf
  let h ← IO.FS.Handle.mk path .read
  let st ← readLoop h st0
  let o := (finish st).outcome
  let dt := (← IO.monoMsNow) - t0
  let what := s!"{label}: {cnf.clauses.size} clauses, {cnf.numLiterals} vars; " ++
    s!"{(o.fmt.map Fmt.name).getD "empty"} LRAT, {o.actions} actions; {dt} ms"
  if o.verified then
    IO.println s!"s VERIFIED UNSAT ({what})"; return 0
  else
    let why := match o.err with | some e => s!"parse error: {e}" | none => resultName o.result
    IO.println s!"s NOT VERIFIED ({why}; {what})"; return 1
