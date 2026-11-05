#!/usr/bin/env bash
# Needs chromedriver. If it is not on PATH, point CHROMEDRIVER at it; on GitHub
# runners, CHROMEWEBDRIVER (the directory holding chromedriver) is used instead.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
log="$here/.lake/conformance.log"
out="$here/.lake/conformance-cases.jsonl"
mkdir -p "$here/.lake"
chromedriver="${CHROMEDRIVER:-${CHROMEWEBDRIVER:+$CHROMEWEBDRIVER/chromedriver}}"
driver=()
if [[ -n "$chromedriver" ]]; then driver=("-Dwebdriver.chrome.driver=$chromedriver"); fi
# `${driver[@]+...}`: bash 3.2 (macOS) treats an empty array as unset under `set -u`
(cd "$here/.." && SNABBDOM_CONFORMANCE=1 sbt -batch ${driver[@]+"${driver[@]}"} "snabbdom/testOnly snabbdom.ConformanceSuite") > "$log" 2>&1 \
  || { tail -40 "$log"; exit 1; }
sed -n 's/^CONFORMANCE //p' "$log" > "$out"
expected="$(sed -n 's/^CONFORMANCE-END //p' "$log")"
actual="$(wc -l < "$out" | tr -d ' ')"
if [[ "$expected" != "$actual" ]]; then
  echo "expected $expected cases, got $actual (output was cut; see $log)"; exit 1
fi
cd "$here"
lake build conform
lake exe conform "$out"
