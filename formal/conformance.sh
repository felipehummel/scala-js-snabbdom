#!/usr/bin/env bash
# Runs the Scala ConformanceSuite in headless Chrome, then replays every case
# with the Lean model (formal/Conform.lean). Fails on any mismatch.
#
# Needs chromedriver. If it is not on PATH, point CHROMEDRIVER at it.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
log="$here/.lake/conformance.log"
out="$here/.lake/conformance-cases.jsonl"
mkdir -p "$here/.lake"
driver=()
if [[ -n "${CHROMEDRIVER:-}" ]]; then driver=("-Dwebdriver.chrome.driver=$CHROMEDRIVER"); fi
(cd "$here/.." && SNABBDOM_CONFORMANCE=1 sbt -batch "${driver[@]}" "snabbdom/testOnly snabbdom.ConformanceSuite") > "$log" 2>&1 \
  || { tail -40 "$log"; exit 1; }
sed -n 's/^CONFORMANCE //p' "$log" > "$out"
expected="$(sed -n 's/^CONFORMANCE-END //p' "$log")"
actual="$(wc -l < "$out" | tr -d ' ')"
if [[ "$expected" != "$actual" ]]; then
  echo "expected $expected cases, got $actual (output was cut; see $log)"; exit 1
fi
cd "$here"
lake build conform >/dev/null
lake exe conform "$out"
