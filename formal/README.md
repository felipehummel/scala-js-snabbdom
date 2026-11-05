# Formal verification of `patch`

This directory proves, in Lean 4, that snabbdom's diff is correct:
**patching an old tree into a new vnode leaves the same DOM that rendering the
new vnode from scratch would**, for every vnode that meets `VNode.WF`: a set of
sufficient conditions on tag and attribute names (see
[Where the property fails](#where-the-property-fails)).

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
   compared through the final DOM only. Last run: 10,004 cases, about 117,000
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
forest (`HeapWF`), `old` agrees with the DOM node by node (`Mirrors`), `old`
itself meets `WF` (together, `PPre`, which is what `patchVnode` expects), and no
DOM exception has happened yet (`ok`). `v.WF` (in `Spec.lean`) says, for every
element, that the tag and the attribute keys are `SafeName`s, and that the keys
are unique (they come from a Scala `Map`), are lowercase, and do not include a
key the selector already sets.

Mounting gives `patch` a `Valid` input, so the theorem covers a mount followed
by any number of patches (`Proofs/Create.lean`):

```lean
theorem createElm_valid (v : VNode) (d : Dom) (hw : HeapWF d) (hok : d.ok = true) (hv : v.WF) :
    Valid (createElm v d).2 (createElm v d).1
```

`createElm_shows` (`Proofs/Create.lean`) is the "from scratch" half:
`createElm v` builds a subtree that shows `v.render`.

## Where the property fails

The library does not have the property for every input. Both cases are run
through the model in `Snabbdom/Counterexamples.lean`, and the conformance suite
checks that the Scala code behaves like the model on them.

`VNode.WF` is sufficient, not necessary. Both failures need the old vnode to
set an attribute that the new one drops (a key the selector also sets) or
re-spells (the same name in another case). The same keys in the new vnode
alone are harmless: patching `div#a` into `div#a` with `{id: "z"}` gives
`id="z"` both ways. `WF` still excludes them from every vnode, because each new
vnode is the old one of the next patch.

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
| `Dom.lean` | The DOM model: nodes with kind, attributes, children and parent; `createElement` and the attribute calls (which lowercase the name), `insertBefore` (with the DOM's own "move if already attached" rule), `removeChild`, `setText`. A misplaced `insertBefore` or `removeChild` sets `ok := false`, standing in for a DOM exception. |
| `Spec.lean` | What "correct" means: `VNode.render`, `Shows`, `Mirrors`, `HeapWF`, `PPre`, `Valid`, and the input restriction `VNode.WF`. |
| `Proofs/Basic.lean` | Each DOM operation keeps the heap well formed; exact effect of `insertBefore` and `removeChild`. |
| `Proofs/Attrs.lean` | The selector's `id`/`class` and the Attributes module: after `create` the element's attributes are `renderAttrs`; after `update` they are exactly the new ones. |
| `Proofs/Create.lean` | `createElm` builds a fresh subtree that shows `v.render` and is a `Valid` input to `patch`. |
| `Proofs/PlaceList.lean` | `placeAroundAnchors`, the reordering loop used when an unkeyed child matched after the common prefix, on plain lists: after it, the reused and new children appear in the new order. This is the hardest lemma. |
| `Proofs/Place.lean` | The same loop on the DOM heap. |
| `Proofs/Children.lean` | Removing unused old children; appending new ones; node identity among siblings. |
| `Proofs/PlaceFewest.lean` | `placeWithFewestMoves`: `longestIncreasingRun` returns indexes whose old positions increase, so keeping those children and moving the rest puts all of them in the new order. |
| `Proofs/Patch.lean` | The child-matching fold: each new child reuses at most one old child (by position if unkeyed, by key otherwise), and the old children not reused are removed. Also the three ways `updateChildren` then places the children: append the new ones when every old child matched in place, `placeAroundAnchors`, or `placeWithFewestMoves`. |
| `Proofs/PatchVnode.lean` | `patchVnode` and the matching fold, by mutual induction. |
| `Proofs/Main.lean` | `patch` (including replacing a node with an incompatible one) and `diff_eq_recreate`. |
| `Axioms.lean` | Fails the build if a main theorem depends on `sorry` or a non-standard axiom. |
| `Counterexamples.lean` | The two inputs above, evaluated in the model. |

## What is not modeled

The proof says nothing about these parts of the library:

* user hooks (`init`, `create`, `insert`, `prepatch`, `update`, `remove`, `destroy`, `post`) and delayed removal
* thunks, SVG (`createElementNS`), and fragments
* exceptions on names. `createElement` and `setAttribute` throw
  `InvalidCharacterError` on an invalid name, such as the empty tag that the
  selector `#a` gives or a key with a space in it. The model accepts every
  name, so `WF` requires `SafeName`: a conservative subset (an ASCII letter,
  then ASCII letters, digits, `-`, `_` or `.`) that browsers accept under both
  the current DOM standard and its older XML `Name` rule.
* the Attributes module's `setAttributeNS` branch. A string value whose key
  starts with `x` and has `:` at index 3 or 5 goes through `setAttributeNS`,
  on any element, not only SVG. The model treats it as `setAttribute`. That
  matches when the key is only ever set to strings (the conformance suite
  checks `xml:lang` and `xlink:href`), but not otherwise: the library throws
  `NamespaceError` on `xmlns:xlink`, and a key set to `true` (through
  `setAttribute`) and then to a string ends with two attributes of that
  name. `SafeName` has no `:`, so `WF` excludes all such keys.
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

The Scala side lives in `snabbdom/src/conformance/`. It compiles with the
other tests but runs only when `SNABBDOM_CONFORMANCE` is set (see `build.sbt`),
so the normal test suite skips it. Nothing runs `lake build` or
`conformance.sh` automatically: CI does neither.
