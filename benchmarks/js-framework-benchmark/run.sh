#!/usr/bin/env bash
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "usage: $0 <js-framework-benchmark dir> [bench args...]" >&2
  exit 1
fi

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
jfb="$1"
shift

if [ ! -d "$jfb" ]; then
  git clone --depth 1 https://github.com/krausest/js-framework-benchmark.git "$jfb"
fi
jfb="$(cd "$jfb" && pwd)"
keyed="$jfb/frameworks/keyed"

echo "==> Building the Scala.js entry"
(cd "$repo" && sbt -batch jsFrameworkBenchmark/fullLinkJS)

echo "==> Installing the entries"
for entry in snabbdom scala-js-snabbdom; do
  rm -rf "${keyed:?}/$entry"
  cp -R "$here/entries/$entry" "$keyed/$entry"
done
mkdir -p "$keyed/scala-js-snabbdom/dist"
cp "$repo"/benchmarks/js-framework-benchmark/scala/target/scala-3*/scala-js-snabbdom-js-framework-benchmark-opt/main.js \
  "$keyed/scala-js-snabbdom/dist/main.js"

echo "==> Building the JavaScript entries"
(cd "$keyed/scala-js-snabbdom" && npm install --silent)
(cd "$keyed/snabbdom" && npm install --silent && npm run build-prod)
(cd "$keyed/react-hooks" && npm ci --silent && npm run build-prod)

echo "==> Installing the benchmark driver"
(cd "$jfb" && npm ci --legacy-peer-deps --silent && npm run install-local)

echo "==> Starting the server"
(cd "$jfb" && npm start) &
server=$!
trap 'kill $server 2>/dev/null || true' EXIT
until curl -sf -o /dev/null http://localhost:8080/index.html; do sleep 1; done

frameworks=(keyed/react-hooks keyed/snabbdom keyed/scala-js-snabbdom)
(cd "$jfb/webdriver-ts" && npm run isKeyed -- --headless true "${frameworks[@]}")
(cd "$jfb" && npm run bench -- "${frameworks[@]}" "$@")
(cd "$jfb" && npm run results)

echo "Raw results: $jfb/webdriver-ts/results"
echo "Table: http://localhost:8080/webdriver-ts-results/dist/index.html (needs 'npm start' in $jfb)"
