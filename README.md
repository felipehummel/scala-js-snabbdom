# scala-js-snabbdom

A fork of [buntec/scala-js-snabbdom](https://github.com/buntec/scala-js-snabbdom),
the Scala.js port of the [Snabbdom](https://github.com/snabbdom/snabbdom)
virtual DOM written by Christoph Bunte. The upstream 0.2.x line (immutable
vnodes, roughly Snabbdom 3.4.0) is the starting point.

## Why this fork exists

Upstream is no longer maintained: its last release is 0.2.0-M3 (2022).

Its 0.2.x child reconciliation matched unkeyed children greedily, comparing each
new child with the next old child of the same tag. One tag change in a sibling
list could cascade: later siblings were patched into the wrong DOM elements,
recreated, or moved with `insertBefore`.

```scala
// before
h("div", List(h("div"), h("div", List(h("my-card"))), h("div")))
// after: only the first child changed from div to p
h("div", List(h("p"), h("div", List(h("my-card"))), h("div")))
```

Upstream creates the `p`, reuses the first old `div` for the card's wrapper and
the card's old wrapper for the last `div`. The original `<my-card>` is removed
and a new one is created.

Recreating or moving a node disconnects it. Custom elements receive
`disconnectedCallback`, a focused input loses focus, and any work owned by the
element is lost.

## What is different

- **Unkeyed children reconcile by position**, as in React and Elm. An unkeyed
  child is matched with the old child at the same index when both are the same
  kind of node (same tag, key and `is`). A mismatch replaces only that node.
  Unkeyed nodes are never moved.
- **Keyed children match by key.** Siblings that share a key are each matched
  at most once. A keyed node is moved only when the new order requires it, never
  when it is already in place. Keyed reordering is not move-minimal.
- **Unmatched comment nodes are removed.** Upstream left them in the DOM.
- **Scala 3 only.** Scala 2.13 is no longer built. CI runs on current GitHub
  Actions with headless Chrome and Firefox.

## Usage

Artifacts are not published to Maven Central. CI publishes only from `v*` tags,
and publishing credentials are not configured. Build a release locally with
`sbt 'set ThisBuild / version := "<version>"' publishLocal` and depend on it:

```scala
libraryDependencies += "io.github.felipehummel" %%% "scala-js-snabbdom" % "<version>"
```

See the test suites for usage examples.

## License

Apache License 2.0, see [LICENSE](LICENSE). Code derived from Snabbdom keeps
its MIT notice (Copyright (c) 2015 Simon Friis Vindum) in the source headers.
