import Garden.CnfSpecs

/-!
# `cnfexport`: write the 22 runs' Lean-generated CNFs as DIMACS

    cnfexport scan <run> <r> <file>        -- `dimacs (Run.cnf R r)`
    cnfexport leaves <run> <dir>           -- per ledger encoding, `body` of the base CNF to
                                           -- <dir>/base<tag>.body; then one manifest line per leaf
    cnfexport leaf <run> <i> <file>        -- `dimacs (Run.leafCnf …)` of leaf i, computed directly
    cnfexport sat13 <file>                 -- the r = 13 leaf that is SAT (positive control)
    cnfexport list                         -- the 22 hypotheses: name, range or r, leaf count

A leaf's CNF is the base's events followed by one unit clause per cube literal, numbered by the
same pass (`CnfRuns.leafCnf_split`): its DIMACS is a header, the base's body, and the cube's lines
(`CnfRuns.dimacs_append`). `leaves` prints, per leaf in list order, `position tag split idx header
cubelines` (tab separated, newlines of `cubelines` written as `|`), so `cnf_certify.py` can hash each leaf without
writing 13,127 files of 19 MB. `leaf` is the slow path the script spot-checks it against.
Glue, not verified: that these functions are the ones written out.
-/

open CnfGen CnfSpecs

def scanRun (name : String) : Option Run := (scanList.find? (·.name == name)).map (·.run)

/-- A split run: its encodings by tag, `r`, and leaves. -/
def leafRun (name : String) : Option ((Nat → Run) × Nat × List Leaf) :=
  (splitList.find? (·.name == name)).map fun x => (x.run, x.r, x.leaves)

def writeDimacs (path : String) (F : List (List Int)) : IO Unit :=
  IO.FS.withFile path .write fun h => do
    h.putStr (header (maxVar F) F.length)
    for c in F do h.putStr (clauseLine c)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>          -- the theorem's 22 hypotheses, from `CnfSpecs.scanList`/`splitList`
    for x in scanList do IO.println s!"scan\t{x.name}\t{x.lo}\t{x.hi}"
    for x in splitList do IO.println s!"split\t{x.name}\t{x.r}\t{x.leaves.length}"
    return 0
  | ["scan", run, r, path] =>
    let some R := scanRun run | IO.eprintln s!"unknown scan {run}"; return 2
    writeDimacs path (R.cnf r.toNat!)
    return 0
  | ["leaf", run, i, path] =>
    let some (R, r, ls) := leafRun run | IO.eprintln s!"unknown run {run}"; return 2
    let some L := ls[i.toNat!]? | IO.eprintln "no such leaf"; return 2
    writeDimacs path ((R L.tag).leafCnf r L.cube)
    return 0
  | ["leaves", run, dir] =>
    let some (R, r, ls) := leafRun run | IO.eprintln s!"unknown run {run}"; return 2
    let tags := (ls.map (·.tag)).eraseDups
    let mut bases : List (Nat × NS × Nat × Nat) := []
    for tag in tags do
      let Rt := R tag
      let base := number (CnfGen.events Rt.n r Rt.tt Rt.o)
      let F := base.out.toList
      IO.FS.withFile s!"{dir}/base{tag}.body" .write fun h => do
        for c in F do h.putStr (clauseLine c)
      bases := bases ++ [(tag, { base with out := #[] }, maxVar F, F.length)]
    let out ← IO.getStdout
    for (L, pos) in ls.zipIdx do
      let some (_, b, nv, m) := bases.find? (·.1 == L.tag) | return 2
      let C := cubeCnf b L.cube
      let hdr := header (max nv (maxVar C)) (m + C.length)
      out.putStrLn s!"{pos}\t{L.tag}\t{L.split}\t{L.idx}\t{(hdr.dropEnd 1).toString}\t{(body C).replace "\n" "|"}"
    return 0
  | ["sat13", path] =>   -- positive control: the r = 13 cube that came back SAT (cube 42, `SPLIT=2`)
    writeDimacs path ((full6 2).leafCnf 13 (tableCube 6 (true, true, false) ++ [pairLit 7 (0, 1)]))
    return 0
  | _ => IO.eprintln "usage: cnfexport list | scan <run> <r> <file> | leaves <run> <dir> | leaf <run> <i> <file> | sat13 <file>"; return 2
