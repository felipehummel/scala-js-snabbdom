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
Snabbdom 3.6.4. Medians of 15 runs (25 for select) in milliseconds, click to
end of paint. Some benchmarks throttle the CPU, the same way for all three.

"Fork before" is the fork before the patching work described below, measured
in the same run as React and Snabbdom JS.

| Benchmark                | React | Snabbdom JS | fork before |
| ------------------------ | ----: | ----------: | ----------: |
| create 1,000 rows        |  43.9 |        41.7 |        55.1 |
| replace all rows         |  54.9 |        46.8 |        75.5 |
| update every 10th row    |  41.0 |        35.9 |       147.5 |
| select row               |  17.6 |        11.7 |       133.9 |
| swap rows                | 149.4 |        38.7 |       227.6 |
| remove row               |  18.5 |        22.1 |        66.6 |
| create 10,000 rows       | 489.9 |       293.8 |       434.7 |
| append 1,000 rows        |  37.3 |        54.6 |        85.1 |
| clear rows               |  26.5 |        29.0 |        38.0 |
| bundle, compressed (KB)  |  51.4 |         4.4 |        50.8 |
| first paint              | 369.1 |        58.8 |       480.3 |
| memory after 1k rows (MB)|   4.4 |         2.9 |         4.5 |

### After the patching work

The fork was measured again in a later run, with Snabbdom JS in the same run as
a control. The machine was busier then (load average about 24), so every time
came out higher. "Adjusted" divides the fork's time by how much slower
Snabbdom JS got between the two runs, then compares it with React.

| Benchmark             | fork now | Snabbdom JS now | fork / JS now | adjusted / React |
| --------------------- | -------: | --------------: | ------------: | ---------------: |
| create 1,000 rows     |     71.2 |            53.6 |          1.33 |             1.26 |
| replace all rows      |     78.1 |            67.0 |          1.17 |             0.99 |
| update every 10th row |     75.5 |            47.6 |          1.59 |             1.39 |
| select row            |     33.5 |            23.5 |          1.43 |             0.95 |
| swap rows             |     77.2 |            60.0 |          1.29 |             0.33 |
| remove row            |     47.0 |            41.2 |          1.14 |             1.36 |
| create 10,000 rows    |    630.6 |           585.8 |          1.08 |             0.65 |
| append 1,000 rows     |     80.7 |            76.7 |          1.05 |             1.54 |
| clear rows            |     29.7 |            37.5 |          0.79 |             0.87 |

Bundle (45.9 KB compressed), first paint and memory stayed within 1.2× of
React. Repeat the run on an idle machine before quoting absolute numbers.

What the profiles showed and what changed:

- Every `patchVnode` converted the old subtree back to a `VNode` and compared
  it with the new one, at each level, so an update that touched two rows still
  walked and allocated the whole table. A patched node now remembers the
  `VNode` it came from, and patching with that same instance (an unchanged
  thunk returns it) is skipped by a reference check.
- Keyed children were placed with a forward scan that moved 997 nodes to swap
  two rows. They are now placed around the longest increasing run of old
  positions, so a swap moves two nodes.
- Event listeners were removed and added again on every patch. The element now
  keeps one listener that dispatches to its current vnode.
- Removing every child clears the parent in one step when no remove hook can
  delay it, and appending to an unchanged list creates and appends without
  matching.
- Smaller allocation cuts in the create path: no closure for empty modules,
  no regex or `split` to build the class attribute, no substring in `h`.

All of the mutable state is private to the library: `PatchedVNode` and the
public API are unchanged for callers.
