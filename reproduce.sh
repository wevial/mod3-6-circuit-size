#!/usr/bin/env bash
# reproduce.sh: check size(MOD3^1_6) = size(MOD3^2_6) = 13 over B2. See README.md.
#
#   ./reproduce.sh fetch     download the pinned tools and Mathlib (the only step that uses the network)
#   ./reproduce.sh quick     fetch if needed; build; Lean proof and axioms; controls; audit of the
#                            Mac record; re-solve all 92 scan CNFs and a seeded sample of 134 leaves
#   ./reproduce.sh full      the same, then re-solve every CNF: 92 scans and 13,347 leaves
#
# Options after the mode: --seed S (quick: the sample's seed), --leaves N (quick: sample size),
# --workers N, --hardest K (full: only the K hardest leaves, by recorded time).
# Needs: Linux on x86-64 (tested) or arm64 (untested), bash, curl, git, gcc/g++, make, python3 >= 3.9, zstd, tar.
# Work files go to $M36_WORK (default ./work): about 10 GB, plus proofs while they are checked.
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$PWD
WORK=${M36_WORK:-$ROOT/work}
export M36_WORK=$WORK XDG_CACHE_HOME=$WORK/cache

# ---------------------------------------------------------------- pins
LEAN_VERSION=4.33.1
LEAN_X86=lean-4.33.1-linux.tar.zst
LEAN_X86_SHA=890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
LEAN_ARM=lean-4.33.1-linux_aarch64.tar.zst
LEAN_ARM_SHA=f7353a8b2a8741c84558523e450556f9a1c45e3cafcf54399ce68c6a24c55f07
CADICAL_COMMIT=c60730422e758ef1cebe7aeddf2dda31c996bf04            # tag rel-3.0.1
CADICAL_TGZ_SHA=2dccd6ecc1878348dd70194d51df6b69006bf86439b5b3c395a5c5dd8863201e
CADICAL_TREE_SHA=37748cdf9f4f366260db706b270254019c9581d13550f935c61efe1472fa21f9
CAKE_COMMIT=a4323b203cc9ecd584ba7da9e3fff08135a09d5f               # tanyongkiam/cake_lpr
CAKE_TGZ_SHA=f4b6d19fef77701dd9796db8268bc5196e2d90415eabd63880e748d2a98ea176
# The three files the checker is built from; these equal the repository's own cake_lpr.sha256.
CAKE_FILES_SHA="3fbd8f31c380e7fb40fede74496ff8b7fb63043645b1afff1e5f26aacdccfa69  basis_ffi.c
2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a  cake_lpr.S
95b64883edc0cb09feedbcb1ebec233e2490f5b458fdda9dc29c212ed916f00c  cake_lpr_arm8.S"

case "$(uname -s)/$(uname -m)" in
  Linux/x86_64) LEAN_ASSET=$LEAN_X86 LEAN_SHA=$LEAN_X86_SHA CAKE_S=cake_lpr.S CAKE_OPT=-O2 ;;
  Linux/aarch64|Linux/arm64) LEAN_ASSET=$LEAN_ARM LEAN_SHA=$LEAN_ARM_SHA CAKE_S=cake_lpr_arm8.S CAKE_OPT= ;;
  *) echo "unsupported platform $(uname -s)/$(uname -m): use Linux x86-64 or arm64 (on a Mac, the Docker recipe in README.md)" >&2; exit 2 ;;
esac
LEAN_DIR=$WORK/tools/lean-$LEAN_VERSION
export PATH=$LEAN_DIR/bin:$PATH

T0=$(date +%s)
step() { printf '\n== [%s, +%ds] %s\n' "$(date -u +%H:%M:%S)" "$(( $(date +%s) - T0 ))" "$*"; }
die() { echo "FAILED: $*" >&2; exit 1; }
treehash() { (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1); }
NPROC=$(python3 -c 'import os; print(len(os.sched_getaffinity(0)))')

download() {   # url sha256 dest
  if [ -f "$3" ] && [ "$(sha256sum "$3" | cut -d' ' -f1)" = "$2" ]; then return; fi
  curl -fsSL --retry 3 -o "$3.part" "$1"
  mv "$3.part" "$3"
}

# ---------------------------------------------------------------- fetch (network)
fetch() {
  mkdir -p "$WORK/dl" "$WORK/tools"
  step "fetch: Lean $LEAN_VERSION toolchain ($LEAN_ASSET)"
  download "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/$LEAN_ASSET" "$LEAN_SHA" "$WORK/dl/$LEAN_ASSET"
  echo "$LEAN_SHA  $WORK/dl/$LEAN_ASSET" | sha256sum -c --quiet - || die "Lean toolchain sha256"
  echo "sha256 $LEAN_SHA ok"

  step "fetch: CaDiCaL rel-3.0.1 ($CADICAL_COMMIT)"
  download "https://codeload.github.com/arminbiere/cadical/tar.gz/$CADICAL_COMMIT" "$CADICAL_TGZ_SHA" "$WORK/dl/cadical.tar.gz"
  if [ "$(sha256sum "$WORK/dl/cadical.tar.gz" | cut -d' ' -f1)" = "$CADICAL_TGZ_SHA" ]; then
    echo "sha256 $CADICAL_TGZ_SHA ok (tarball)"
  else   # GitHub may recompress archives; then the extracted files must match
    rm -rf "$WORK/dl/cadical-check"; mkdir -p "$WORK/dl/cadical-check"
    tar -C "$WORK/dl/cadical-check" --strip-components=1 -xzf "$WORK/dl/cadical.tar.gz"
    [ "$(treehash "$WORK/dl/cadical-check")" = "$CADICAL_TREE_SHA" ] || die "CaDiCaL sha256 (tarball and file tree)"
    echo "tarball differs; file-tree sha256 $CADICAL_TREE_SHA ok"
  fi

  step "fetch: cake_lpr ($CAKE_COMMIT)"
  download "https://codeload.github.com/tanyongkiam/cake_lpr/tar.gz/$CAKE_COMMIT" "$CAKE_TGZ_SHA" "$WORK/dl/cake_lpr.tar.gz"
  [ "$(sha256sum "$WORK/dl/cake_lpr.tar.gz" | cut -d' ' -f1)" = "$CAKE_TGZ_SHA" ] \
    && echo "sha256 $CAKE_TGZ_SHA ok (tarball)" || echo "the tarball differs from the pinned sha256 (GitHub may recompress); checking its source files"
  rm -rf "$WORK/dl/cake-check"; mkdir -p "$WORK/dl/cake-check"
  tar -C "$WORK/dl/cake-check" --strip-components=1 -xzf "$WORK/dl/cake_lpr.tar.gz"
  (cd "$WORK/dl/cake-check" && echo "$CAKE_FILES_SHA" | sha256sum -c --quiet - && sha256sum -c --quiet cake_lpr.sha256) || die "cake_lpr source sha256"
  echo "basis_ffi.c, cake_lpr.S, cake_lpr_arm8.S: sha256 as pinned and as in its cake_lpr.sha256"

  step "fetch: Mathlib and its dependencies at lean/lake-manifest.json's commits"
  python3 - "$ROOT/lean/lake-manifest.json" > "$WORK/dl/packages.tsv" <<'PY'
import json, sys
for p in json.load(open(sys.argv[1]))['packages']:
    print('%s\t%s\t%s' % (p['name'], p['url'], p['rev']))
PY
  while IFS=$'\t' read -r name url rev; do
    d=$ROOT/lean/.lake/packages/$name
    if [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" != "$rev" ]; then
      rm -rf "$d"; mkdir -p "$d"
      git -C "$d" init -q
      git -C "$d" remote add origin "$url"
      git -C "$d" fetch -q --depth 1 origin "$rev"
      git -C "$d" -c advice.detachedHead=false checkout -q FETCH_HEAD
    fi
    [ "$(git -C "$d" rev-parse HEAD)" = "$rev" ] || die "$name is not at $rev"
    printf '%-18s %s\n' "$name" "$rev"
  done < "$WORK/dl/packages.tsv"

  unpack_lean
  step "fetch: Mathlib's compiled .olean files (lake exe cache get)"
  (cd "$ROOT/lean" && lake exe cache get) 2>&1 | tr '\r' '\n' | { grep -v '^Downloaded:' || true; } | tail -3
  touch "$WORK/.fetched"
}

unpack_lean() {
  if [ ! -x "$LEAN_DIR/bin/lake" ]; then
    echo "$LEAN_SHA  $WORK/dl/$LEAN_ASSET" | sha256sum -c --quiet - || die "Lean toolchain sha256"
    mkdir -p "$LEAN_DIR"
    tar -C "$LEAN_DIR" --strip-components=1 --use-compress-program=unzstd -xf "$WORK/dl/$LEAN_ASSET"
  fi
}

# ---------------------------------------------------------------- build (offline)
build_tools() {
  unpack_lean
  step "build: CaDiCaL"
  if [ ! -x "$WORK/tools/cadical/build/cadical" ]; then
    rm -rf "$WORK/tools/cadical"; mkdir -p "$WORK/tools/cadical"
    tar -C "$WORK/tools/cadical" --strip-components=1 -xzf "$WORK/dl/cadical.tar.gz"
    [ "$(treehash "$WORK/tools/cadical")" = "$CADICAL_TREE_SHA" ] || die "CaDiCaL source tree sha256"
    (cd "$WORK/tools/cadical" && ./configure > configure.log 2>&1 && make -j"$NPROC" > make.log 2>&1) || die "CaDiCaL build (see work/tools/cadical/*.log)"
  fi
  "$WORK/tools/cadical/build/cadical" --version

  step "build: cake_lpr from $CAKE_S"
  if [ ! -x "$WORK/tools/cake_lpr/cake_lpr" ]; then
    rm -rf "$WORK/tools/cake_lpr"; mkdir -p "$WORK/tools/cake_lpr"
    tar -C "$WORK/tools/cake_lpr" --strip-components=1 -xzf "$WORK/dl/cake_lpr.tar.gz"
    (cd "$WORK/tools/cake_lpr" && echo "$CAKE_FILES_SHA" | sha256sum -c --quiet - && sha256sum -c --quiet cake_lpr.sha256) || die "cake_lpr source sha256"
    (cd "$WORK/tools/cake_lpr" && gcc $CAKE_OPT basis_ffi.c "$CAKE_S" -o cake_lpr -std=c99) || die "cake_lpr build"
  fi
  echo "basis_ffi.c, $CAKE_S: sha256 as pinned and as in cake_lpr.sha256"

  step "build: lratdirect, cnfexport, lratcheck (lean/direct: Lean core and Std only)"
  (cd "$ROOT/lean/direct" && lake build 2>&1 | tail -1)
  # The sources these executables are built from are byte-identical to those of the Mac run
  # (results/mac_recheck_provenance.txt, section 1).
  (cd "$ROOT/lean" && sha256sum -c --quiet <<'SUMS') || die "Lean sources of the checkers differ from the Mac run's"
36e0122f772145c33af89576c49faf4dfb4ece0855a0975e67ca1f78496d8b52  Garden/LratDirect.lean
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
62b42448a11a5db045035d766409ec52422832b0c5b62e209d404e748dd95b59  LratDirect.lean
aab06d19d360bafba96f32253601688633244f8a0646d8eedd50cd22aa6cc271  Garden/CnfSpecs.lean
add228f26b132566bc57c66d6ab572ffbc14dac64dff96957ebcf670d5226320  Garden/CnfLeaves.lean
bac464ca4817903bb2b08cc12833621400cf8625d34c44d7783ebf2da62879cd  Garden/CnfGen.lean
c9efa79f9e5afc50190c5521db6d34d088ce2273a8735799c4116638b9bdf005  CnfExport.lean
fc8b0b6f98913761437656b87788a5a1c7c36e4921d32f8ee067743c8481c713  Garden/LratStream.lean
SUMS
  echo "their Lean sources have the sha256 of the Mac run's (results/mac_recheck_provenance.txt)"
  (cd "$WORK/tools" && sha256sum cadical/build/cadical cake_lpr/cake_lpr) | sed 's/^/binary /'
  (cd "$ROOT/lean/direct/.lake/build/bin" && sha256sum lratdirect cnfexport lratcheck) | sed 's/^/binary /'
}

lean_proof() {
  step "Lean: build the proof (lean/, with Mathlib)"
  (cd "$ROOT/lean" && lake build 2>&1 | tail -2)
  step "Lean: axioms of the main theorems"
  (cd "$ROOT/lean" && lake env lean Axioms.lean) | tee "$WORK/axioms.out"
  python3 - "$WORK/axioms.out" <<'PY' || die "axioms"
import re, sys
text = open(sys.argv[1]).read()
items = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text.replace('\n', ' '))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [(n, a) for n, a in items if not {x.strip() for x in a.split(',') if x.strip()} <= allowed]
if len(items) != 13 or bad or 'does not depend on any axioms' in text:
    sys.exit('unexpected axioms: %d theorems listed, %s' % (len(items), bad))
print('AXIOMS OK: all 13 theorems use only propext, Classical.choice, Quot.sound (no sorryAx, no native_decide)')
PY
}

# ---------------------------------------------------------------- main
MODE=${1:-}
[ $# -gt 0 ] && shift
case "$MODE" in
  fetch) fetch; step "fetch done"; exit 0 ;;
  quick|full) ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac

[ -f "$WORK/.fetched" ] || fetch
build_tools
lean_proof
step "Lean: must-fail controls and witnesses (lean/controls/)"
python3 scripts/lean_controls.py
step "re-check: export the split runs' bases"
python3 -B scripts/recheck.py prepare
step "re-check: audit the Mac record (results/mac_recheck_results.tsv) against this job list"
python3 -B scripts/recheck.py audit
step "re-check: runtime controls (both checkers must reject altered proofs)"
python3 -B scripts/recheck.py controls
if [ "$MODE" = quick ]; then
  step "re-check: all 92 scan CNFs and a seeded sample of leaves"
  python3 -B scripts/recheck.py run quick "$@"
else
  step "re-check: every CNF"
  python3 -B scripts/recheck.py run full "$@"
fi
step "ALL CHECKS PASSED ($MODE)"
