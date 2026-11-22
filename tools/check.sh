#!/usr/bin/env bash
# Run the Lemmata pipeline locally -- the same steps, in the same order, that the cluster
# runs on every push to main:
#
#   1. validate   manifests, docs<->lean pairing, labels, snippet markers, DOIs, umbrella,
#                 plus the tests of the tools (tests/adversarial.mjs, tests/scope.mjs)
#   2. build      lake build of the Lean modules (Mathlib from the cache)
#   3. kernel     lemmata-replay re-checks every declaration of those modules in Lean's kernel
#   4. audit      lemmata-check: axiom policy over ALL their declarations, namespaces, exports
#   5. render     MyST static HTML into docs/_build/html, with the verification panels
#
#   tools/check.sh                      everything, for every entry: what the cluster does
#   tools/check.sh --changed [<base>]   only the entries your changes touch (since <base>;
#                                       default: where your branch left origin/main), and every
#                                       entry that imports them
#   tools/check.sh --entry <id> ...     only these entries (id or LeanName; repeat --entry),
#                                       and every entry that imports them
#   tools/check.sh ... --no-docs        stop after the audit (fast loop while writing Lean)
#
# A partial check (--changed, --entry) builds what its entries import from other entries but
# re-checks and audits only their own modules; the rest is unchanged, and the cluster checks the
# whole archive on every commit. It runs the full check by itself when a change can affect every
# entry (lean/lakefile.toml, the toolchain, checker/, tools/). The render always covers the whole
# site; entries outside a partial check are shown as not verified.
#
# Locally the verifier is built from ./checker. In the cluster it comes from the
# deployment's own copy, so a change to ./checker in a content PR has no effect there.
set -euo pipefail
cd "$(dirname "$0")/.."
step() { printf '\n\033[1m== %s\033[0m\n' "$*"; }

docs=1; scope_args=()
while (( $# )); do
  case "$1" in
    --no-docs) docs=0 ;;
    --entry) [[ $# -ge 2 && ${2:0:2} != -- ]] || { echo "--entry needs an entry id or LeanName"; exit 2; }
             scope_args+=(--entry "$2"); shift ;;
    --changed) if [[ $# -ge 2 && ${2:0:2} != -- ]]; then scope_args+=(--changed "$2"); shift; else scope_args+=(--changed); fi ;;
    -h|--help) awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    *) echo "unknown option $1 (tools/check.sh --help)"; exit 2 ;;
  esac
  shift
done

step "1/5 validate"
node tools/lemmata.mjs validate
# The tools must refuse hostile input (file-reading directives outside an entry, ids that
# name built-ins) and show each result's own Lean statement (not a decoy in a comment or
# another namespace); a partial check must cover what a change can affect. Quiet unless
# something fails.
mkdir -p out
node tests/adversarial.mjs > out/adversarial.log 2>&1 || { cat out/adversarial.log; echo "adversarial tests FAILED"; exit 1; }
echo "adversarial tests: ok ($(grep -c '^ok ' out/adversarial.log) cases)"
node tests/scope.mjs > out/scope-tests.log 2>&1 || { cat out/scope-tests.log; echo "scope tests FAILED"; exit 1; }
echo "scope tests: ok ($(grep -c '^ok ' out/scope-tests.log) cases)"

# What this run covers: everything, or (--changed, --entry) some entries.
mode=full
rm -f out/scope.json out/verification.json
if (( ${#scope_args[@]} )); then
  node tools/lemmata.mjs scope "${scope_args[@]}" --out out/scope.json
  mode=$(node -e 'console.log(require("./out/scope.json").mode)')
fi
field() { node -e 'const s = require("./out/scope.json"); console.log((s[process.argv[1]] ?? []).join("\n"))' "$1"; }

step "2/5 lake build"
case $mode in
  full)   ( cd lean && lake exe cache get >/dev/null && lake build ) ;;
  scoped) # Every module of the covered entries (also those nothing imports); Lake adds what
          # they import. The umbrella, which imports every entry, is left out.
          field modules | sed 's/^/+/' > out/build.targets
          ( cd lean && lake exe cache get >/dev/null && xargs lake build < ../out/build.targets ) ;;
  none)   echo "no Lean module is affected: nothing to build" ;;
esac

if [[ $mode != none ]]; then
  # Same rule as the cluster's verify step: no compiled module without a source -- a leftover
  # from a deleted file (or from another clone sharing .lake/build) would otherwise be
  # checked. In the full check also the converse: every source module compiled.
  ( cd lean && { find Lemmata -name '*.lean' | sed 's/\.lean$//'; echo Lemmata; } | LC_ALL=C sort ) > out/source.modules
  # (`if`, not `&&`: a partial check does not build the umbrella, and a failing test as the last
  # command of the group would end the script here, silently, under set -e and pipefail.)
  ( cd lean/.lake/build/lib/lean && { find Lemmata -name '*.olean' | sed 's/\.olean$//'; if [ -f Lemmata.olean ]; then echo Lemmata; fi; } | LC_ALL=C sort ) > out/compiled.modules
  stale=$(LC_ALL=C comm -13 out/source.modules out/compiled.modules)
  if [[ -n $stale ]] || { [[ $mode == full ]] && ! diff -q out/source.modules out/compiled.modules >/dev/null; }; then
    diff -u out/source.modules out/compiled.modules | sed -n '3,40p' || true
    echo "compiled modules without source (or vice versa): delete lean/.lake/build and rebuild"
    exit 1
  fi
  if [[ $mode == full ]]; then tr '/' '.' < out/compiled.modules > out/replay.modules; else field modules > out/replay.modules; fi

  n=$(wc -l < out/replay.modules | tr -d ' ')
  step "3/5 kernel check (lemmata-replay, $n module$( (( n == 1 )) || echo s))"
  ( cd checker && lake build -q )
  # One pass: what the modules import from outside the list (Mathlib, and in a partial check
  # the other entries) is loaded once, and every declaration of the listed modules goes
  # through the kernel again (checker/Replay.lean).
  ( cd lean && lake env ../checker/.lake/build/bin/lemmata-replay ../out/replay.modules </dev/null )

  step "4/5 axiom audit, namespaces, export bindings (lemmata-check)"
  if [[ $mode == full ]]; then node tools/lemmata.mjs request out/request.json
  else node tools/lemmata.mjs request out/request.json --scope out/scope.json; fi
  ( cd lean && lake env ../checker/.lake/build/bin/lemmata-check ../out/request.json ../out/verification.json )
  echo "lemmata-check: ok ($(node -e 'const r=require("./out/verification.json");console.log(r.declarations_audited+" declarations, axioms used: "+(r.archive_axioms.join(", ")||"none"))'))"
fi

summary() {
  case $mode in
    full)   echo "all checks passed" ;;
    scoped) echo "partial check passed: $(field entries | paste -sd, - | sed 's/,/, /g')$(field dirs | grep -qx Shared && echo ', lean/Lemmata/Shared')." \
                 "Other entries were not re-checked here; the cluster checks everything." ;;
    none)   echo "no Lean module is affected: validate$( (( docs )) && echo ' and render') passed" ;;
  esac
}
if (( ! docs )); then echo; summary; exit 0; fi

# The render needs a report; without Lean steps it is a preview. A partial report covers only
# its entries, and prepare shows the others as not verified.
if [[ -f out/verification.json ]]; then report=(out/verification.json); else report=(--preview); fi

step "5/5 render"
node tools/lemmata.mjs prepare "${report[@]}" --commit "$(git rev-parse HEAD 2>/dev/null || echo local)"
( cd docs && HOST=127.0.0.1 ../node_modules/.bin/myst build --config myst.runtime.yml --html --strict --ci --keep-host )
# The cluster adds these in site-index; locally the preview needs them too.
node tools/lemmata.mjs enhance docs/_build/html

# The same render the way the cluster does it: a copy of what would be committed -- tracked
# files plus new ones git does not ignore, so a freshly scaffolded entry is included before
# `git add` (it was not: the umbrella imported files the copy lacked) -- with no git
# history, .lemmata/provenance.json added as the controller would, LEMMATA_BUILD=1,
# and validate before prepare. Catches tool changes that only break inside the build Job
# (2026-10-19: validate refused the cluster's own .lemmata/ and every build failed).
step "5b/5 render as in the cluster"
SIM=$(mktemp -d)
trap 'rm -rf "$SIM"' EXIT
git ls-files -z --cached --others --exclude-standard | tar --null -T - -cf - | tar -xf - -C "$SIM"
mkdir -p "$SIM/.lemmata"
# `provenance` prints what the controller would ship for HEAD, computed from local git.
node tools/lemmata.mjs provenance > "$SIM/.lemmata/provenance.json"
# Chained with && on purpose: set -e is suspended inside a `( ... ) || ...` list, so
# without it a failing validate would not stop the chain (the first version of this
# step passed with the bug it was written for reinstated).
REPO=$(pwd)
( export LEMMATA_ROOT="$SIM" LEMMATA_BUILD=1 &&
  node tools/lemmata.mjs validate &&
  node tools/lemmata.mjs prepare "${report[@]}" --commit "$(git rev-parse HEAD)" >/dev/null &&
  cd "$SIM/docs" &&
  HOST=127.0.0.1 "$REPO/node_modules/.bin/myst" build --config myst.runtime.yml --html --strict --ci --keep-host >"$SIM/render.log" 2>&1 ) \
  || { echo "cluster-style render FAILED"; grep -E "⛔|Error" "$SIM/render.log" | head -20; exit 1; }
echo "cluster-style render: ok"
# And offline, as the build Job renders: network refused except MyST's own local server,
# with the theme step 5 already downloaded. Anything that needs the internet while
# rendering -- an unresolved DOI link, say -- fails here instead of in the cluster.
THEME="$REPO/docs/_build/templates/site/myst/book-theme"
if [[ -d $THEME ]]; then
  ( export LEMMATA_ROOT="$SIM" LEMMATA_BUILD=1 LEMMATA_THEME="$THEME" &&
    node tools/lemmata.mjs prepare "${report[@]}" --commit "$(git rev-parse HEAD)" >/dev/null &&
    cd "$SIM/docs" && rm -rf _build &&
    HTTPS_PROXY=http://127.0.0.1:9 HTTP_PROXY=http://127.0.0.1:9 NO_PROXY=localhost,127.0.0.1 NODE_USE_ENV_PROXY=1 \
    HOST=127.0.0.1 "$REPO/node_modules/.bin/myst" build --config myst.runtime.yml --html --strict --ci --keep-host >"$SIM/offline.log" 2>&1 ) \
    || { echo "offline render FAILED (the cluster renders without internet):"; grep -E "⛔|Error" "$SIM/offline.log" | head -20; exit 1; }
  echo "offline render: ok"
fi
echo
summary
echo "Preview: npx serve docs/_build/html  (or: npm run preview)"
