#!/bin/sh
# Typeset mod3-6-note.pdf: ./build.sh  (needs only docker; about 30 s once the image is present)
#
# The figures in fig/ were generated from the original repository's records and checked against
# them there (the circuit against Mod3Upper.lean and the decoded SAT model, evaluated on all 64
# inputs; the cube tree against the ledgers and CnfLeaves.lean; the counts and times against the
# re-check results). This copy only typesets. The PDF is byte-reproducible: its dates come from
# SOURCE_DATE_EPOCH, and the image is pinned by digest (texlive/texlive:TL2025-historic).
set -eu
IMAGE=texlive/texlive@sha256:7056390eac37715fd3e01875037ceb4016cb17d44c611f7bbbfa7a012007979f
EPOCH=1792972800   # 2026-10-26T00:00:00Z, the note's date
HERE=$(cd "$(dirname "$0")" && pwd)
docker run --rm --network none --memory 8g --cpus 4 --user "$(id -u):$(id -g)" -e HOME=/tmp \
  -e SOURCE_DATE_EPOCH=$EPOCH -e FORCE_SOURCE_DATE=1 -v "$HERE":/note -w /note "$IMAGE" sh -c '
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/b mod3-6-note.tex >/tmp/b.out 2>&1 ||
    { tail -40 /tmp/b.out; exit 1; }
  grep -E "LaTeX Warning|Overfull|undefined" /tmp/b/mod3-6-note.log || true
  cp /tmp/b/mod3-6-note.pdf /note/mod3-6-note.pdf'
echo "build.sh: wrote $HERE/mod3-6-note.pdf"
