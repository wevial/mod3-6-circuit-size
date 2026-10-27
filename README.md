# size(MOD3^1_6) = size(MOD3^2_6) = 13 over B2

`MOD3^r_n(x) = [x_1 + … + x_n ≡ r (mod 3)]`. B2 is the full binary basis: each gate can compute any of the 16 Boolean functions of its two inputs. The size of a function is the least number of gates in a circuit that computes it.

**Claim.** No 12-gate B2 circuit computes `MOD3^1_6` or `MOD3^2_6`. Both have size exactly 13.

This repository holds a Lean 4 proof of that claim and the evidence for its hypotheses. Each hypothesis says that every formula in a specified family is unsatisfiable: no assignment of truth values satisfies it. The formulas are in conjunctive normal form (CNF), 13,439 in all. Every one has been re-solved as a Boolean satisfiability (SAT) problem. Each proof, in the LRAT format, has been accepted by two independently verified checkers.

**Reproduce it.** One command, `./reproduce.sh quick`, rebuilds the proof and re-checks a sample of the CNFs on your machine. `./reproduce.sh full` re-checks all of them.

**The argument, in 7 pages:** [`note/mod3-6-note.pdf`](note/mod3-6-note.pdf). It covers the encoding, the symmetry breaks and gate-elimination bounds, the cube split, and the verification chain, with figures. This README is the reference for the package itself.

**Who did this.** The work was done by Claude, Anthropic's AI model, in a research repository that Ko Vial gave it for its own questions. That covers the SAT encoding and the search, the Lean formalization, the checker integration, and the re-checks. This package comes from that repository. The Lean sources are unchanged. Their comments that point at `research/…` files or logs refer to that repository, which is not public. The findings from those files are summarized below, with supporting records in `results/`.

## Background

- D. E. Knuth, *The Art of Computer Programming*, Vol. 4B, §7.2.2.2 (Satisfiability), answer to exercise 480; first in Vol. 4, Fascicle 6 (2015). It gives the exact sizes of `MOD3^r_n` for n ≤ 5 and `MOD3^0_6 = 12`. It calls the cases n = 6, r ≠ 0 *still unknown*, and conjectures size `3n − 5 − [(n + r) ≡ 0 (mod 3)]`, which is 13 for both.
- A. S. Kulikov, D. Pechenev, N. Slezkin, *SAT-based circuit local improvement*, MFCS 2022, arXiv:2102.12579. Gives a 13-gate circuit for these functions.

So the open question was whether 12 gates suffice. Web searches on 2026-10-23 and 2026-10-24 found no later resolution. They covered Knuth's errata to April 2026, the papers citing Kulikov–Pechenev–Slezkin that could be reached, and the MOD3 experiments in Kulikov's own repository. A shorter check on 2026-10-26 (web search, and the 2026 commits in that repository) found nothing new. That is evidence about the search, not proof that nobody has done it.

## The theorems

All theorems are in `lean/` (Lean 4.33.1, Mathlib at the commit in `lean/lake-manifest.json`). Each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. `reproduce.sh` prints the axioms, from `lean/Axioms.lean`.

**The circuit model** (`Garden/CircuitDual.lean`, about 15 lines; read these yourself).
- A circuit is a list of gates. A gate is `⟨a, b, op⟩`: two node indices and any table `op : Bool → Bool → Bool`.
- The nodes are the inputs, then the gates in order. Gate `i` reads nodes `a` and `b`, and an index that is not yet defined reads `false`. The output is the last node.
- `Computes r gs` means `gs ≠ []` and the output equals `mod3 r x` on all 64 inputs `x ∈ {0,1}^6`.
- `LB m g s` (`Garden/Mod3SemBounds.lean`) means every nonempty gate list that computes `g` on all `m`-bit inputs has at least `s` gates.

Every B2 circuit in the usual sense is such a list, once any gates after the output are deleted. So `LB 6 (mod3 r) 13` says every B2 circuit for `MOD3^r_6` has at least 13 gates. The model's extras, reading a constant `false` or a later node as `false`, only add circuits.

**Upper bound.** `Mod3Upper.mod3_1_upper : Computes 1 c13`, for an explicit 13-gate list `c13`, by `decide` on all 64 inputs. `CircuitDual.mod3_6_size_dual` shows that negating inputs costs no gates, which turns a circuit for one residue into one for the other. `Mod3Upper.mod3_2_upper` uses it to give a 13-gate circuit for `MOD3^2_6`.

**Lower bound, with CNF hypotheses.** The statement of `CnfRuns.mod3_6_size_13` (`Garden/CnfRuns.lean`) is

```
(LB 6 (mod3 1) 13 ∧ ∃ gs, gs.length = 13 ∧ Computes 1 gs) ∧
(LB 6 (mod3 2) 13 ∧ ∃ gs, gs.length = 13 ∧ Computes 2 gs)
```

It has 22 hypotheses, one per SAT run, and nothing else. Each hypothesis has one of two forms:

- `ScanUnsat R lo hi`: for every `r` with `lo ≤ r ≤ hi`, `(toCNF (R.cnf r)).Unsat`.
- `LeavesUnsat R r leaves`: for every leaf `L` of a cube tree, `(toCNF ((R L.tag).leafCnf r L.cube)).Unsat`.

Here `R.cnf r` is the CNF for "a circuit of `r` gates satisfying run `R`'s constraints computes `f`". A Lean function generates it (`Garden/CnfGen.lean`). A cube fixes some variables; `leafCnf` adds those fixed values as unit clauses (one literal each). `Unsat` is `Std.Sat.CNF.Unsat`, the property that Lean core's verified LRAT checker concludes. No hypothesis mentions circuits: the step from circuits to CNFs is proved.

The 22 runs are listed in `CnfSpecs.scanList` and `splitList` (`cnfexport list` prints them). A scan checks a range of gate counts; a split run checks the leaves of a cube tree:

| function | hypotheses | CNFs |
|---|---|---|
| `MOD3^q_3`, q = 0, 1, 2 | scans r ≤ 2, 3, 3 | 8 |
| `MOD3^q_4` | scans r ≤ 6, 6, 5 | 17 |
| `MOD3^q_5` | scans r ≤ 8 (each q); r = 9 split into 60 leaves for q = 0 and for q = 2 | 24 + 120 |
| six restricted functions used by `w2_5^1`'s bounds | scans r ≤ 3, 3, 2, 6, 5, 6 | 25 |
| `w2_5^1 = [2x_0 + x_1 + x_2 + x_3 + x_4 ≡ 1 (mod 3)]` | scan r ≤ 7; r = 8 and r = 9, each 50 leaves | 7 + 100 |
| `MOD3^1_6` | scan r ≤ 11 (`elim6`); r = 12 split into 13,127 leaves (`full6_12`) | 11 + 13,127 |

That is 92 scan CNFs and 13,347 leaf CNFs, 13,439 in all. The r = 12 tree has 2,352 cubes on the first gate's table and the second and third gates' inputs. 69 of these are refined into 36 children each, and 190 of those children into 45 grandchildren each.

The Lean proof connects circuits to CNFs in these steps:

- A minimum circuit can be put in the CNF's shape at the same size (`Reduction.shape_of_min`).
- It can be put in a canonical form that satisfies the symmetry breaks: gate order, symmetric-input order, the first gate's inputs and table (`SymCanon.canonical`, `Reduction.minimal_canonical_on`).
- Every added constraint holds in that form. The redundancy bounds `elim`, `elim2`, `sem`, `semxor` and `semeq` come from the sizes of smaller functions (`GateElim.sem_bound`, `Mod3SemBounds`, `W2SemBounds`). Those sizes are proved from their own runs (`Mod3Tower.mod3_6_lower_sat`). That is why the table includes the n = 3, 4, 5 rows and `w2_5^1`.
- Such a circuit satisfies the generated CNF (`CnfSound.adm_sat`).
- The cube trees cover every circuit, whatever leaves the data lists (`CnfRuns.tree_cover`).
- So if all 22 CNF families are unsatisfiable, `MOD3^1_6` has size at least 13. `MOD3^2_6` follows by duality.

`CnfRuns.mod3_6_size_13_lists` states the same theorem with its hypotheses taken from `scanList` and `splitList`.

**Lower bound, with checker hypotheses.** `DirectRuns.mod3_6_size_13_direct` (`Garden/DirectRuns.lean`) has the same conclusion. Its hypotheses are:

```
∀ x ∈ scanList, ∀ r, x.lo ≤ r → r ≤ x.hi → ∃ bs, (checkJob (.scan x.name r) bs).verified = true
∀ x ∈ splitList, ∀ i < x.leaves.length,  ∃ bs, (checkJob (.leaf x.name i) bs).verified = true
```

`checkJob` is the function the `lratdirect` executable runs. It looks the job up by name in `scanList`/`splitList`, and builds that CNF in memory (`Job.cnf?`; `scan_cnf?` and `leaf_cnf?` prove it is the hypothesis's CNF). It then passes the proof's bytes `bs`, block by block, to Lean core's LRAT checker (`compactLratChecker`). `LratDirect.check_sound` proves that if `check cnf bs` is verified, then `cnf.Unsat`, whatever the parser read from the bytes. So each hypothesis of this theorem is "`lratdirect scan|leaf <name> <r|i> <proof>` accepted some proof file", and no DIMACS file (a text representation of a CNF) is involved.

**Positive controls.**
- At r = 13, cube 42 of the full encoding is satisfiable. Its model decodes to `c13`, the circuit of `Mod3Upper.lean`. `cnf_certify.out` records that this model satisfies every clause of Lean's r = 13 CNF for that cube.
- `CnfRuns.cnf13_sat` is the conditional version: under the 22 hypotheses, the r = 13 CNF is satisfiable. So if the hypotheses hold, what they rule out is 12 gates, not every size.

**Must-fail controls** (`lean/controls/`). These 35 statements must fail Lean's elaboration check. Each is a slightly wrong version of a proof step. Examples: one literal flipped in a generated clause, a scan range one short, the final theorem claiming 14, a leaf dropped, the checker also accepting `outOfProof`. Two witness files show that several of the mutated claims are actually false. Each control's comment says what it changes. `scripts/lean_controls.py` checks that each one fails with the error its mutation causes, using one pattern per control taken from the logs where the controls were written. It also rejects any error outside a control.

## What is verified and what remains trusted

**Verified by the Lean kernel:**
- Everything from "these 22 families of CNFs are unsatisfiable" to "`MOD3^1_6` and `MOD3^2_6` have size 13".
- The upper bound.
- The soundness of `lratdirect`'s checking function.

**Trusted on the formal side, whoever builds it:**
- The Lean kernel.
- The model definitions, read by eye (above).
- Mathlib's compiled `.olean` files. The original work and `reproduce.sh` both use Mathlib's prebuilt cache for the pinned commit, as is usual. The Garden files are elaborated and kernel-checked where they are built, but the Mathlib declarations they import are not re-checked. To remove this reliance on the cache, compile Mathlib from source (several hours on 4 cores; not timed here):

  ```
  rm -rf lean/.lake/packages/*/.lake lean/.lake/build
  (cd lean && PATH="$PWD/../work/tools/lean-4.33.1/bin:$PATH" lake build)
  ```

  The executables `lratdirect`, `cnfexport` and `lratcheck` do not involve Mathlib at all.

**Established by computation, outside the kernel:** the CNFs are unsatisfiable. On 2026-10-25 every one of the 13,439 CNFs was re-solved on one machine, an Apple M4 Pro laptop (macOS 26.6.2), with CaDiCaL 3.0.1, in one session of 11 h 35 min on 12 workers. Each proof was accepted by two independently verified checkers:
- `lratdirect`, against the CNF built in memory;
- `cake_lpr`, against the DIMACS file. It is CakeML's LRAT/LPR checker, verified down to machine code with its DIMACS parser included, at commit `a4323b20`, from `cake_lpr_arm8.S`.

Every leaf's DIMACS file had the sha256 hash recorded for it in the original search's ledger. The record is `results/mac_recheck_results.tsv`, one line per CNF, with 0 failures.

The record relies on the following:

- **The run, as a record.** Each line of `mac_recheck_results.tsv` records that the driver accepted both verdicts for one CNF. The verdicts are stored in normalized form. The exact acceptance conditions were checked by the driver as it ran and cannot be recovered from the file:
  - `cake_lpr`'s stdout exactly `s VERIFIED UNSAT`. It exits 0 on failure too.
  - `lratdirect` exits 0 with one line naming the job.

  `results/mac_recheck_pins.txt` pins the binaries and inputs by sha256. A path bug in the driver left the Lean sources out of the pins. `results/mac_recheck_provenance.txt` ties those sources to the binaries. The run's sources equal the ones in this repository (`reproduce.sh` checks this). Rebuilding from them on that machine gave the pinned `lratdirect` and `cnfexport` byte for byte.
- **`lratdirect`'s trusted parts.** Its read loop (`readLoop` and `main` in `lean/LratDirect.lean`, about ten lines, read by eye) and the compiled code: the Lean compiler and runtime, `Std.HashMap` in `CnfGen.number`, file reads, and core's compiled LRAT checker.
- **`cake_lpr`'s trusted parts.** CakeML's own verification (HOL4 proofs that are not replayed here), and the fact that the distributed `cake_lpr_arm8.S` is that verified compiler's output: its sha256 matches the `cake_lpr` repository's own `cake_lpr.sha256`. Its unverified C shim `basis_ffi.c` (file I/O, command line, heap, exit). Its build: Apple clang 21 assembling the `.S` and linking the shim, and the macOS loader. The link from the Lean CNF to the file `cake_lpr` reads also requires trust: `cnfexport`'s compiled DIMACS writer. A leaf's file is assembled as header + base body + cube lines, which `CnfRuns.dimacs_append` proves is that leaf's DIMACS. For every leaf, the file's sha256 also equals the ledger's. These are therefore the bytes the original Python encoder wrote on a different machine; the Lean compiler did not produce those original bytes. A scan's file is compared with `cnf_certify.out`'s sha256, which comes from another Lean export. The Lean compiler is thus the one component in both checking routes: it built `lratdirect` and the writer of `cake_lpr`'s input. For every leaf, the ledger's sha256 is a second witness to that input that does not depend on the Lean compiler.
- **The scripts.** The driver's acceptance logic and its job list: every `(scan, r)` and every leaf of `cnfexport list`, 92 + 13,347. Also the Python that ran it (Xcode's Python 3.9.6). The driver as run is `results/as-run/mac_recheck.py`; one comment in this copy has a personal name removed. A review found three weaknesses that did not affect this run:
  - resuming trusted any line ending in OK, but the run was one session that started with 0 done;
  - its controls would have counted a crash as a rejection, but the recorded output shows explicit rejections;
  - a disk-check race could stop the run, but could not record a false OK.

  `scripts/recheck.py` fixes all three:
  - a resumed run validates every earlier line: it must follow a session header with the same pins (the binaries, the script, the ledgers, the exported bases), every field must be valid, and no CNF may have two OK lines;
  - a control counts only an explicit rejection;
  - a proof that is not on disk counts as still to be written.
- **sha256**, for the pins and the DIMACS-to-ledger comparison.
- **The machine and macOS**, common to both checkers.

Given the shared parts (the job list, the driver, the record, the machine), a wrong verdict needs both checkers' own trusted parts to fail on the same CNF. The solver needs no trust, because its proofs are checked.

**When you run `reproduce.sh` here**, the record above is re-established on your machine, partly in `quick` and completely in `full`. In place of the record, the Mac and its Python, you then trust:
- your machine;
- `lratdirect` and `cnfexport`, compiled from the same sources by the Lean 4.33.1 toolchain for your platform;
- `scripts/recheck.py`;
- a `cake_lpr` built by your `gcc`.

On x86-64 that `cake_lpr` is built from `cake_lpr.S`, CakeML's verified x64 output, so the second checker differs from the Mac's in its machine code and its CPU. The CaDiCaL you build needs no trust.

## Reproduce

Use Linux on x86-64 (tested) or arm64 (the same steps with the arm64 downloads and `cake_lpr_arm8.S`; not tested). You need bash, curl, git, gcc/g++, make, python3 ≥ 3.9 (standard library only), zstd and tar. Allow about 15 GB of disk for tools, Mathlib and work files, plus room for proofs while they are checked.

The largest proof was for leaf 10389: 3.4 GB on the Mac, 5.5 GB on the x86-64 machine below. The driver starts a CNF only if free disk would stay above 10 GB (`M36_DISK_FLOOR_GB`) after every running proof reaches its estimate (4 MB per recorded second, plus 50 MB). So `full` needs about 20 GB free after installation to start the hardest leaf, and more to run several hard leaves at once. 8 GB of RAM is enough.

```
./reproduce.sh fetch     # the only step that uses the network
./reproduce.sh quick     # (runs fetch first if needed)
./reproduce.sh full      # every CNF; about 130 CPU-hours
```

**`fetch`** downloads the following, each checked against a pin at the top of `reproduce.sh`. Any mismatch stops it.

- The Lean 4.33.1 release tarball, by its sha256.
- CaDiCaL `rel-3.0.1` (`c6073042`), by the tarball's sha256. If GitHub has recompressed the archive, the sha256 of the extracted file tree is checked instead, and that tree hash is checked again before every build.
- `cake_lpr` `a4323b20`. The three files the checker is built from (`basis_ffi.c`, `cake_lpr.S`, `cake_lpr_arm8.S`) are checked by sha256, both against the pins and against that repository's own `cake_lpr.sha256`. This happens at fetch and again before the build. The tarball's sha256 is also reported.
- Mathlib and its dependencies, each a shallow git fetch of the exact commit in `lean/lake-manifest.json`, so git checks the commit hash.
- Mathlib's compiled cache for that commit (`lake exe cache get`). It has no pin of ours: Mathlib's cache tool chooses the files by the hashes of the pinned sources.

Nothing else uses the network. The Docker recipe below runs every later step with `--network none`.

**`quick`** then runs:

1. **Tools.** Builds CaDiCaL (`./configure && make`) and `cake_lpr` (`gcc basis_ffi.c cake_lpr.S`, or `cake_lpr_arm8.S` on arm64). Builds `lratdirect`, `cnfexport` and `lratcheck` from `lean/direct/`, a package with no Mathlib. Checks that the Lean sources of `lratdirect` and `cnfexport` have the sha256 recorded for the Mac run.
2. **Proof.** `lake build` of the whole proof, then prints the axioms of 13 theorems (`lean/Axioms.lean`). Fails unless they are within the standard three.
3. **Lean controls.** Each of the 35 must-fail controls fails with the error its mutation causes, and both witness files build.
4. **Audit of the record.** Re-derives the job list from this `cnfexport` and the ledgers. Then checks `results/mac_recheck_results.tsv` field by field: exactly one valid OK line for each of the 13,439 CNFs, each with sha256 equal to the recorded one, CaDiCaL exit 20, and both verdicts. No other lines.
5. **Runtime controls.** For scan `best4_0` r = 6 and leaf `full6_12` 6844, both checkers must accept the real proof. Both must then reject, explicitly (not by crashing), the proof given for another CNF and the proof with one bit flipped at four places. The other CNFs are scan `best4_1` r = 6, and leaves 6845 and 6843. Leaf 6843 has the same header as 6844 and a different cube.
6. **Re-check.** All 92 scan CNFs, and a uniform sample of 134 of the 13,347 leaves (1%), are processed as on the Mac:
   - export the CNF and match its sha256;
   - solve with CaDiCaL to a binary LRAT proof;
   - accept only if CaDiCaL exits 20, `cake_lpr` exits 0 printing exactly `s VERIFIED UNSAT`, and `lratdirect` exits 0 with its one line naming the job.

   The sample is drawn from a seed. Choose your own with `--seed <any string>`, so that the sample is not one I picked. `--leaves N` changes its size.

**`full`** runs steps 1–5, then re-checks every CNF: the scans, then the leaves, hardest first. A failed CNF stops new starts. To resume, rerun the same command. Every earlier line is validated before it is skipped (see the trust list above). A CNF that failed is tried again, and a later valid OK line for it is reported alongside the failure. `full --hardest K` runs only the K leaves with the largest recorded times.

Results go to `work/results-*.tsv`, one line per CNF, the same columns as the Mac record. `python3 scripts/recheck.py summary <file>` validates a file against the current binaries and the job selection its session lines record, then summarizes it.

**In Docker**, as tested on x86-64. On an Apple-silicon Mac, Docker Desktop would take the untested arm64 path.

```
docker build -t mod3-6 - <<'EOF'
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl git python3 zstd && rm -rf /var/lib/apt/lists/*
EOF
docker volume create mod3-6
docker run --rm --memory 8g --cpus 4 -v mod3-6:/m36 -v "$PWD":/src:ro mod3-6 \
  bash -c 'cp -a /src/. /m36/ && /m36/reproduce.sh fetch'
docker run --rm --network none --memory 8g --cpus 4 -v mod3-6:/m36 mod3-6 /m36/reproduce.sh quick
```

## Timings

These timings were measured on 2026-10-26, in Docker (`--memory 8g --cpus 4`) on an x86-64 machine (AMD Ryzen 7 H 255). Each run started from an empty volume and used the code in this repository. `fetch` ran with the network, and every later step with `--network none`.

**`quick`** passed (`ALL CHECKS PASSED`, 226/226 CNFs OK):

| step | wall |
|---|---|
| `fetch`: Lean toolchain, CaDiCaL, `cake_lpr`, Mathlib and 8 dependencies, Mathlib's cache | 64 s |
| build CaDiCaL (34 s), `cake_lpr`, `lratdirect`/`cnfexport`/`lratcheck` | 41 s |
| build the Lean proof (the 19 Garden files; Mathlib from its cache) | 102 s |
| axioms; Lean controls | 5 s; 19 s |
| export the split runs' bases; audit of the Mac record | 3 s; 1 s |
| runtime controls | 195 s |
| re-check of 92 scans and 134 sampled leaves, 4 workers | 1,812 s |
| **`quick` in all** | **36 min 18 s**, plus 64 s for `fetch` |

The re-check took 1.99 CPU-hours: CaDiCaL 1.21, `lratdirect` 0.55, `cake_lpr` 0.22. It wrote and deleted 10.4 GB of proofs. Peak RSS was 2,054 MiB for `cake_lpr` (its heap), 477 MiB for `lratdirect` and 142 MiB for CaDiCaL. That is 1.36 times the CPU time the Mac's record shows for the same 226 CNFs. After `quick`, the work directory held 5.4 GB and `lean/.lake` 7.1 GB.

**`full` on the three hardest leaves** (`./reproduce.sh full --hardest 3`, by recorded time, in a second container alongside `quick`). Seconds of wall time per process, and the proof size:

| leaf | recorded (ledger) | CaDiCaL | proof | `cake_lpr` | `lratdirect` | wall | the Mac: CaDiCaL, proof, `cake_lpr`, `lratdirect` |
|---|---|---|---|---|---|---|---|
| `full6_12` 10397 | 2,016 | 1,095 | 2.09 GB | 119 | 361 | 26 min 14 s | 665, 2.23 GB, 92, 359 |
| `full6_12` 10389 | 1,535 | 2,681 | 5.47 GB | 260 | 667 | 60 min 8 s | 1,112, 3.43 GB, 157, 583 |
| `full6_12` 12317 | 1,373 | 995 | 2.19 GB | 140 | 410 | 25 min 45 s | 586, 2.20 GB, 95, 362 |

All three were OK, with no failures (`ALL CHECKS PASSED (full)`). The three ran at once, and steps 1–5 took 361 s, so the command took 66 min 11 s in all. Peak RSS was 2,053 MiB for `cake_lpr`, 809 MiB for `lratdirect` and 166 MiB for CaDiCaL. CaDiCaL's proofs differ between the two machines, as solver runs on different hardware and compilers can; each was checked on its own machine.

**`full`** was not run here. On the Mac it took 128.4 CPU-hours: CaDiCaL 66.4, `lratdirect` 46.1, `cake_lpr` 15.9; 11 h 35 min on 12 workers. At the ratio measured on the `quick` sample, this machine would need about 175 CPU-hours, roughly two days on 4 CPUs. The hardest leaves ran slower than that ratio here, so treat it as a rough figure.

## Layout

- `reproduce.sh`: fetch, build and check, as above.
- `lean/`: the Lake project.
  - `Garden/`: the 19 files of the proof, the import closure of `CnfRuns`, `DirectRuns` and `Mod3Upper`/`CircuitDual`.
  - `CnfExport.lean`, `LratDirect.lean` and `LratCheck.lean`: the executables.
  - `Axioms.lean`.
  - `direct/`: the Std-only package for the executables.
  - `controls/`: the must-fail controls and witnesses.
- `note/`: the technical note (`mod3-6-note.pdf`), its LaTeX source and figures, and `build.sh`, which typesets it byte-for-byte in a pinned TeX Live image.
- `scripts/recheck.py`: the re-check driver; `scripts/lean_controls.py`: the Lean controls.
- `results/`:
  - `mac_recheck_results.tsv` and `mac_recheck_summary.out`: the full re-check.
  - `mac_recheck_pins.txt` and `mac_recheck_provenance.txt`: its pins.
  - `mac_recheck_controls.out`, `mac_recheck_control2.out` and `mac_recheck_probe.out`: its controls and its `cake_lpr` heap probe.
  - `direct_check.out`: an earlier check of all 92 scans and a 1% leaf sample, with `lratdirect` and Lean's `lratcheck`, in a Linux container.
  - `cnf_certify.out`: the first certification. It recorded scan sha256 values, matched every leaf to its ledger by sha256, and holds the r = 13 positive control.
  - `ledgers/`: the original search's records, one line per leaf with its cube and its DIMACS sha256. They are used here only for the sha256 comparison and for ordering leaves by difficulty.
  - `as-run/`: the scripts that produced these files.

## License

Apache License 2.0; see `LICENSE`. CaDiCaL, `cake_lpr` and Mathlib are downloaded under their own licenses, not included.
