#!/usr/bin/env bash
# Run the full Lemmata pipeline locally -- the same steps, in the same order, that the
# cluster runs on every push to main:
#
#   1. validate   manifests, docs<->lean pairing, labels, snippet markers, umbrella
#   2. build      lake build of every Lemmata.* module (Mathlib from the cache)
#   3. kernel     leanchecker re-checks our modules' declarations in the kernel
#   4. audit      lemmata-check: axiom policy over ALL our declarations + export bindings
#   5. render     MyST static HTML into docs/_build/html, with the verification panels
#
#   tools/check.sh            all five steps
#   tools/check.sh --no-docs  stop after the audit (fast loop while writing Lean)
#
# Locally the verifier is built from ./checker. In the cluster it comes from the
# deployment's own copy, so a change to ./checker in a content PR has no effect there.
set -euo pipefail
cd "$(dirname "$0")/.."
step() { printf '\n\033[1m== %s\033[0m\n' "$*"; }

step "1/5 validate"
node tools/lemmata.mjs validate

step "2/5 lake build"
( cd lean && lake exe cache get >/dev/null && lake build )

step "3/5 kernel check (leanchecker)"
( cd lean && LEAN_NUM_THREADS=1 lake env leanchecker Lemmata </dev/null )
echo "leanchecker: ok"

step "4/5 axiom audit + export bindings (lemmata-check)"
( cd checker && lake build -q )
mkdir -p out
node tools/lemmata.mjs request out/request.json
( cd lean && lake env ../checker/.lake/build/bin/lemmata-check ../out/request.json ../out/verification.json )
echo "lemmata-check: ok ($(node -e 'const r=require("./out/verification.json");console.log(r.declarations_audited+" declarations, axioms used: "+(r.archive_axioms.join(", ")||"none"))'))"

[[ "${1:-}" == "--no-docs" ]] && exit 0

step "5/5 render"
node tools/lemmata.mjs prepare out/verification.json --commit "$(git rev-parse HEAD 2>/dev/null || echo local)"
( cd docs && HOST=127.0.0.1 ../node_modules/.bin/myst build --config myst.runtime.yml --html --strict --ci --keep-host )

# The same render the way the cluster does it: a copy of the tracked files (no git
# history), with .lemmata/provenance.json added as the controller would, LEMMATA_BUILD=1,
# and validate before prepare. Catches tool changes that only break inside the build Job
# (2026-10-19: validate refused the cluster's own .lemmata/ and every build failed).
step "5b/5 render as in the cluster"
SIM=$(mktemp -d)
trap 'rm -rf "$SIM"' EXIT
git ls-files -z | tar --null -T - -cf - | tar -xf - -C "$SIM"
mkdir -p "$SIM/.lemmata"
# `provenance` prints what the controller would ship for HEAD, computed from local git.
node tools/lemmata.mjs provenance > "$SIM/.lemmata/provenance.json"
# Chained with && on purpose: set -e is suspended inside a `( ... ) || ...` list, so
# without it a failing validate would not stop the chain (the first version of this
# step passed with the bug it was written for reinstated).
REPO=$(pwd)
( export LEMMATA_ROOT="$SIM" LEMMATA_BUILD=1 &&
  node tools/lemmata.mjs validate &&
  node tools/lemmata.mjs prepare out/verification.json --commit "$(git rev-parse HEAD)" >/dev/null &&
  cd "$SIM/docs" &&
  HOST=127.0.0.1 "$REPO/node_modules/.bin/myst" build --config myst.runtime.yml --html --strict --ci --keep-host >/dev/null 2>&1 ) \
  || { echo "cluster-style render FAILED"; exit 1; }
echo "cluster-style render: ok"
echo
echo "all checks passed. Preview: npx serve docs/_build/html  (or: npm run preview)"
