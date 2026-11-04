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
Snabbdom 3.6.4. All three entries ran in the same run, so they shared the
machine's load (load average 17 to 35 during the run; absolute times are high,
the ratios are what to read). Times are in milliseconds, click to end of
paint: median, then the interquartile range and the run count. Some benchmarks
throttle the CPU, the same way for all three. Memory, bundle size and first
paint are single runs.

| Benchmark | React | Snabbdom JS | fork | fork / React |
| --- | ---: | ---: | ---: | ---: |
| create 1,000 rows | 47.4 (43.8–56.4, n=15) | 48.5 (41.5–54.0, n=15) | 66.1 (56.2–73.0, n=15) | 1.39 |
| replace all rows | 58.2 (53.6–65.8, n=15) | 62.8 (58.4–67.3, n=15) | 76.7 (67.3–81.7, n=15) | 1.32 |
| update every 10th row | 51.6 (49.9–58.0, n=15) | 46.8 (42.1–50.1, n=15) | 72.0 (71.3–77.6, n=15) | 1.40 |
| select row | 21.0 (20.1–21.6, n=25) | 18.7 (17.4–21.5, n=25) | 24.2 (22.6–25.6, n=25) | 1.15 |
| swap rows | 251.2 (244.8–323.6, n=15) | 47.0 (44.6–51.0, n=15) | 59.4 (56.7–67.7, n=15) | 0.24 |
| remove row | 35.6 (34.2–36.3, n=15) | 33.3 (30.9–34.0, n=15) | 37.0 (36.0–39.3, n=15) | 1.04 |
| create 10,000 rows | 770.8 (747.8–815.1, n=15) | 690.4 (606.5–734.2, n=15) | 591.2 (554.0–674.4, n=15) | 0.77 |
| append 1,000 rows | 64.2 (57.2–66.2, n=15) | 63.5 (59.8–65.7, n=15) | 88.1 (83.8–92.1, n=15) | 1.37 |
| clear rows | 44.1 (41.1–46.5, n=15) | 47.2 (36.1–55.0, n=15) | 34.0 (32.8–35.5, n=15) | 0.77 |
| memory, ready (MB) | 1.1 | 0.6 | 1.4 | 1.25 |
| memory, 1,000 rows (MB) | 4.4 | 2.9 | 4.8 | 1.08 |
| memory, 1,000 rows cleared (MB) | 2.0 | 0.8 | 1.8 | 0.92 |
| bundle, compressed (KB) | 51.4 | 4.4 | 46.1 | 0.90 |
| first paint | 621.1 | 96.9 | 464.1 | 0.75 |

Every case is within 2x of React in this run; the slowest are create, update
and append, at about 1.4x. They were not profiled again after the last change.

Before the patching work, measured the same way in an earlier, quieter run,
the fork was 3.6x React on update every 10th row, 7.6x on select, 3.6x on
remove row and 2.3x on append.

What changed:

- Every `patchVnode` converted the old subtree back to a `VNode` and compared
  it with the new one, at each level, so an update that touched two rows still
  walked and allocated the whole table. A patched element now keeps the
  `VNode` it was built from whenever that `VNode` equals the conversion, so an
  unchanged thunk (which answers with that `VNode`) is skipped by a reference
  check, and an equal rebuilt subtree by a comparison that allocates nothing.
- Keyed children were placed with a forward scan that moved 997 nodes to swap
  two rows. They are now placed around the longest increasing run of old
  positions, so a swap moves two nodes.
- Event listeners were removed and added again on every patch. The element now
  keeps one listener that dispatches to its current vnode.
- Appending to an unchanged list creates and appends without matching.
- Smaller allocation cuts in the create path: no closure for empty modules,
  no regex to build the class attribute.

All of the mutable state is private to the library: `PatchedVNode` and the
public API are unchanged for callers.
