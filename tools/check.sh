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
echo
echo "all checks passed. Preview: npx serve docs/_build/html  (or: npm run preview)"
