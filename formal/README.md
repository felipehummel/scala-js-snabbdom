# Formal verification of `patch`

This directory proves, in Lean 4, that snabbdom's diff is correct:
**patching an old tree into a new vnode leaves the same DOM that rendering the
new vnode from scratch would**, for every vnode whose attributes meet two
conditions the library needs (see [Where the property fails](#where-the-property-fails)).

It has two parts:

1. **A proof about a model.** `Snabbdom/Model.lean` transcribes `init.scala`
   (`createElm` with its selector parsing, `patchVnode`, `updateChildren`,
   `patch`) and the Attributes module into Lean, on top of a small DOM
   (`Snabbdom/Dom.lean`). The theorems in `Snabbdom/Proofs/` are about that
   model. They have no `sorry` and use only Lean's three standard axioms;
   `Snabbdom/Axioms.lean` checks this on every `lake build`.
2. **A bridge from the model to the Scala code.** Lean cannot read Scala, so
   `conformance.sh` runs the real library in headless Chrome on 10,000 random
   `(old, new)` pairs plus the two counterexamples below. A recording `DomApi`
   logs every structural DOM call (create, insert, append, remove, set text).
   The Lean model then replays each case and must make the same calls in the
   same order and leave the same DOM. Attribute writes do not go through
   `DomApi` (the Scala code calls `setAttribute` on the element), so they are
   compared through the final DOM only. Last run: 10,002 cases, about 116,000
   DOM operations, 0 mismatches.

So the guarantee is: the algorithm, as modeled, is proved correct for every
input that meets `VNode.WF`; and the model matches the Scala implementation on
every input tested, including inputs outside `VNode.WF`. The second half is
testing, not proof. A Scala behavior that the generator never exercises could
still differ from the model.

## The theorems

`Snabbdom/Proofs/Main.lean`:

```lean
theorem diff_eq_recreate (old : PNode) (v : VNode) (d d0 : Dom) (h : Valid d old) (hv : v.WF)
    (hw0 : HeapWF d0) (t : DTree) :
    Shows (patch old v d).2 (patch old v d).1.node t ↔
      Shows (createElm v d0).2 (createElm v d0).1.node t
```

Whatever tree you read from the DOM at the patched node, you read exactly the
same tree after `createElm v` in any well-formed DOM, and vice versa.

It follows from `patch_correct`, which also says where the result is and what
else changed:

```lean
theorem patch_correct (old : PNode) (v : VNode) (d : Dom) (h : Valid d old) (hv : v.WF) :
    Valid (patch old v d).2 (patch old v d).1 ∧
    (patch old v d).1.toVNode = v ∧
    Shows (patch old v d).2 (patch old v d).1.node v.render ∧
    (∀ i, i < d.next → i ∉ old.ids → d.parentNode old.node ≠ some i →
      (patch old v d).2.nodes i = d.nodes i) ∧
    (∀ p px, d.parentNode old.node = some p → d.nodes p = some px →
      (patch old v d).2.nodes p =
        some { px with children := replaceIn old.node (patch old v d).1.node px.children }) ∧
    (d.parentNode old.node = none → ...)
```

In order: the DOM is still well formed and no DOM exception happened; the
returned tree describes `v`; the DOM shows `v.render` at the returned node;
nothing outside `old`'s subtree changed, except that the parent now holds the
new node where the old one was; and a detached root stays detached.

`Valid d old` is what `patch` expects of its input: the DOM is a well-formed
forest (`HeapWF`), no DOM exception has happened yet (`ok`), `old` agrees with
the DOM node by node (`Mirrors`), and `old` itself meets `WF`. `v.WF` (in
`Spec.lean`) says, for every element, that attribute keys are unique (they
come from a Scala `Map`), are lowercase, and do not include a key the selector
already sets.

`createElm_shows` (`Proofs/Create.lean`) is the "from scratch" half:
`createElm v` builds a subtree that shows `v.render`.

## Where the property fails

The library does not have the property for every input. Both cases are run
through the model in `Snabbdom/Counterexamples.lean`, and the conformance suite
checks that the Scala code behaves like the model on them. `VNode.WF` excludes
them.

* **An attribute the selector also sets.** `createElm` sets `id` from `#…` and
  `class` from `.…` with `setAttribute`, outside the Attributes module. The
  module's update does not know about them. Patch `div#a` with
  `attrs = {id: "z"}` into `div#a` with no attrs: the vnodes are `sameVnode`,
  the update removes `id`, and the element ends with no `id`. Rendering
  `div#a` from scratch gives `id="a"`. The same happens with `div.x` and a
  `class` attribute.
* **Attribute names that are not lowercase.** The DOM lowercases the name in
  `setAttribute` and `removeAttribute`; the Attributes module compares names
  as written. Patch `{TITLE: "x"}` into `{title: "y"}`: the update sets
  `title="y"`, then removes `TITLE`, which the DOM reads as `title`. Rendering
  from scratch keeps `title="y"`.

## How the proof is split

| File | What it proves |
| --- | --- |
| `Dom.lean` | The DOM model: nodes with kind, attributes, children and parent; `insertBefore` (with the DOM's own "move if already attached" rule), `removeChild`, `setText`, attribute calls (which lowercase the name). Invalid calls set `ok := false`, standing in for a DOM exception. |
| `Spec.lean` | What "correct" means: `VNode.render`, `Shows`, `Mirrors`, `HeapWF`, `Valid`, and the input restriction `VNode.WF`. |
| `Proofs/Basic.lean` | Each DOM operation keeps the heap well formed; exact effect of `insertBefore` and `removeChild`. |
| `Proofs/Attrs.lean` | The selector's `id`/`class` and the Attributes module: after `create` the element's attributes are `renderAttrs`; after `update` they are exactly the new ones. |
| `Proofs/Create.lean` | `createElm` builds a fresh subtree that shows `v.render`. |
| `Proofs/PlaceList.lean` | The child reordering loop on plain lists: after it, the reused and new children appear in the new order. This is the hardest lemma. |
| `Proofs/Place.lean` | The same loop on the DOM heap. |
| `Proofs/Children.lean` | Removing unused old children; appending new ones; node identity among siblings. |
| `Proofs/Patch.lean` | The child-matching fold: each new child reuses at most one old child (by position if unkeyed, by key otherwise), and the old children not reused are removed. |
| `Proofs/PatchVnode.lean` | `patchVnode` and the matching fold, by mutual induction. |
| `Proofs/Main.lean` | `patch` (including replacing a node with an incompatible one) and `diff_eq_recreate`. |
| `Axioms.lean` | Fails the build if a main theorem depends on `sorry` or a non-standard axiom. |
| `Counterexamples.lean` | The two inputs above, evaluated in the model. |

## What is not modeled

The proof says nothing about these parts of the library:

* user hooks (`init`, `create`, `insert`, `prepatch`, `update`, `remove`, `destroy`, `post`) and delayed removal
* thunks, SVG namespaces (`createElementNS`, `setAttributeNS`), and fragments
* the Props, Class, Style, Dataset and EventListeners modules (only Attributes is modeled)
* the first patch of a raw DOM element, `patch(elm: dom.Element, vnode)`. It
  wraps `elm` with `emptyNodeAt`, which keeps its tag, id and classes but
  claims no children and no other attributes whatever `elm` holds, so `Valid`
  does not hold for such an `elm` and the
  property can fail: patching a `<div>` that already contains the text `hi`
  into `div [text "a"]` appends, leaving both texts. The conformance suite
  only uses this entry point to mount `old` on an empty placeholder.
* the DOM throwing `HierarchyRequestError` when a node is inserted into its own descendant (`patch` never does that, but the DOM model does not check it)
* the order in which attributes were set (the model compares attribute maps, not insertion order)

Comment nodes are never reused by `sameVnode`, which matches the Scala code.

## Running it

Install Lean with [elan](https://github.com/leanprover/elan) (`brew install elan-init`, then `elan default stable`). The toolchain version is pinned in `lean-toolchain`.

Check the proofs:

```bash
lake build
```

Run the conformance check against the Scala code (needs sbt and a chromedriver
matching your Chrome; point `CHROMEDRIVER` at it if it is not on `PATH`):

```bash
CHROMEDRIVER=/path/to/chromedriver ./conformance.sh
```

The Scala side lives in `snabbdom/src/conformance/` and is only compiled when
`SNABBDOM_CONFORMANCE` is set (see `build.sbt`), so it does not run with the
normal test suite.
