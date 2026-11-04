# js-framework-benchmark entry

Measures this fork against [Snabbdom](https://github.com/snabbdom/snabbdom)
(JavaScript) and React with
[krausest/js-framework-benchmark](https://github.com/krausest/js-framework-benchmark),
the usual benchmark for UI libraries. It times each operation from the click to
the end of the paint, using Chrome traces.

## Entries

- `scala/`: the Scala.js app, built by the `jsFrameworkBenchmark` sbt project.
- `entries/scala-js-snabbdom/`: the benchmark's wrapper for that app.
- `entries/snabbdom/`: the same app written in JavaScript against Snabbdom
  3.6.4. The benchmark no longer ships a Snabbdom entry, so this one is ours.
- React: the benchmark's own `keyed/react-hooks` entry.

All three are keyed. The two Snabbdom apps mirror each other line for line and
render each row as a `thunk`, the counterpart of the `memo` rows in
`react-hooks`. A row thunk must put the row's key in the vnode its function
returns as well, because the Scala.js thunk copies its data from that vnode.

## Running

```bash
benchmarks/js-framework-benchmark/run.sh ../js-framework-benchmark --headless true
```

The script clones the benchmark if the directory does not exist, builds the
three entries, checks they are keyed, runs every benchmark, and builds the
result table. Arguments after the directory go to `npm run bench`, for example
`--benchmark 01_ 07_` or `--count 5`.

Run it from a regular checkout. sbt-git cannot open a git worktree, so sbt
fails to load the build there.

## Results, 2026-11-04

Headless Chrome on an Apple M5 Pro, benchmark commit `fa510a7`, React 19.2.0,
Snabbdom 3.6.4. All three entries ran in the same run. The machine was busy
with other processes (load average 10 to 22), and js-framework-benchmark runs
the entries one after another within each benchmark, so the load can differ
between the cells of a row. Absolute times are inflated; read the ratios.
Times are in milliseconds, click to end of paint: median, then the
interquartile range and the run count. Some benchmarks throttle the CPU, the
same way for all three. Memory figures are single runs. Bundle size and first
paint are single runs from an earlier build the same day, whose bundle is
within 0.1 KB of the current one.

| Benchmark | React | Snabbdom JS | fork | fork / React |
| --- | ---: | ---: | ---: | ---: |
| create 1,000 rows | 37.6 (32.5–41.9, n=15) | 37.5 (36.3–41.2, n=15) | 44.9 (44.3–48.0, n=15) | 1.19 |
| replace all rows | 47.2 (40.1–50.4, n=15) | 50.5 (48.2–52.4, n=15) | 61.6 (58.1–62.5, n=15) | 1.31 |
| update every 10th row | 41.0 (39.1–42.3, n=15) | 34.4 (33.1–35.2, n=15) | 57.6 (55.8–58.7, n=15) | 1.40 |
| select row | 15.0 (13.5–16.5, n=25) | 13.4 (12.6–14.2, n=25) | 18.4 (17.5–19.3, n=25) | 1.23 |
| swap rows | 185.3 (174.1–203.5, n=15) | 38.3 (36.4–40.7, n=15) | 45.7 (43.5–47.4, n=15) | 0.25 |
| remove row | 29.3 (29.1–30.9, n=15) | 29.2 (26.1–31.1, n=15) | 32.3 (31.1–32.8, n=15) | 1.10 |
| create 10,000 rows | 702.3 (659.2–735.5, n=15) | 499.7 (492.0–520.5, n=15) | 512.7 (499.5–568.4, n=15) | 0.73 |
| append 1,000 rows | 56.3 (56.0–59.5, n=15) | 54.6 (54.0–55.1, n=15) | 66.2 (64.8–73.6, n=15) | 1.18 |
| clear rows | 35.2 (34.2–36.8, n=15) | 31.6 (30.4–32.2, n=15) | 31.2 (29.8–33.5, n=15) | 0.89 |
| memory, ready (MB) | 1.2 | 0.6 | 1.4 | 1.17 |
| memory, 1,000 rows (MB) | 4.4 | 2.9 | 4.8 | 1.08 |
| memory, 1,000 rows cleared (MB) | 2.0 | 0.8 | 1.8 | 0.93 |
| bundle, compressed (KB) | 51.4 | 4.4 | 46.1 | 0.90 |
| first paint | 621.1 | 96.9 | 464.1 | 0.75 |

Every case is within 2x of React in this run. The slowest are update every
10th row (1.40x) and replace all rows (1.31x).

## How the fork patches

- A patched element keeps the `VNode` it was built from whenever that `VNode`
  equals the conversion `toVNode` would build. An unchanged thunk answers with
  that `VNode`, so skipping it is a reference check, and an equal rebuilt
  subtree is found equal by a comparison that allocates nothing. An update
  that touches two rows therefore does not walk the whole table.
- Keyed children are placed around the longest increasing run of their old
  positions, so swapping two rows moves two nodes.
- An element keeps one event listener across patches, which dispatches to its
  current vnode, so a patch adds or removes only the event names that changed.
- When every old child matches the new child at its own position, the rest
  of the new children are created and appended without a key lookup.
- Modules iterate their maps without allocating a tuple per entry, styles and
  props skip empty maps on create, and the class attribute is built without a
  regex.

All of the mutable state is private to the library: `PatchedVNode` and the
public API are unchanged for callers.
