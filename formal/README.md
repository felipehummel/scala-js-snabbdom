# Formal verification of `patch`

This directory proves, in Lean 4, that snabbdom's diff is correct:
**patching an old tree into a new vnode leaves the same DOM that rendering the
new vnode from scratch would**, for every vnode that meets `VNode.WF`: valid
tag and attribute names, and one key per attribute (see
[What `VNode.WF` excludes](#what-vnodewf-excludes)).

It has two parts:

1. **A proof about a model.** `Snabbdom/Model.lean` transcribes `init.scala`
   (`createElm` with its selector parsing, `patchVnode`, `updateChildren`,
   `patch`) and the Attributes module into Lean, on top of a small DOM
   (`Snabbdom/Dom.lean`). The theorems in `Snabbdom/Proofs/` are about that
   model. They have no `sorry` and use only Lean's three standard axioms;
   `Snabbdom/Axioms.lean` checks this on every `lake build`.
2. **A bridge from the model to the Scala code.** Lean cannot read Scala, so
   `conformance.sh` runs the real library in headless Chrome on 10,000 random
   `(old, new)` pairs (a tenth of them with up to 12 mostly keyed siblings, for
   `placeWithFewestMoves`) plus a few fixed cases. A recording
   `DomApi` logs every structural DOM call (create, insert, append, remove, set
   text). The Lean model then replays each case and must make the same calls
   in the same order and leave the same DOM. Attribute writes do not go through
   `DomApi` (the Scala code calls `setAttribute` on the element), so they are
   compared through the final DOM only. Last run: 10,005 cases, about 153,000
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
element, that the tag is a `SafeName`, that every attribute key is an
`AttrName` (a `SafeName`, or `xml:`, `xmlns:` or `xlink:` then one), and that
no two keys name the same attribute (`attrName`: the key lowercased, unless it
is namespaced).

Mounting gives `patch` a `Valid` input, so the theorem covers a mount followed
by any number of patches (`Proofs/Create.lean`):

```lean
theorem createElm_valid (v : VNode) (d : Dom) (hw : HeapWF d) (hok : d.ok = true) (hv : v.WF) :
    Valid (createElm v d).2 (createElm v d).1
```

`createElm_shows` (`Proofs/Create.lean`) is the "from scratch" half:
`createElm v` builds a subtree that shows `v.render`.

## What `VNode.WF` excludes

`VNode.WF` is sufficient, not necessary. It asks for two things:

* **Names from a conservative subset.** `createElement`, `setAttribute` and
  `setAttributeNS` throw `InvalidCharacterError` or `NamespaceError` on some
  names, and the model has no such exceptions. `WF` keeps to names that never
  throw: an ASCII letter, then ASCII letters, digits, `-`, `_` or `.`,
  optionally after `xml:`, `xmlns:` or `xlink:` for a key. This also leaves out
  names the DOM accepts, such as `_x`, `foo:bar` or non-ASCII names (see
  "exceptions on names" below).
* **One key per attribute,** so not `title` and `TITLE` in one map.
  `createElm` writes both, to the same DOM attribute, in the order the Scala
  `Map` iterates, which the vnode does not determine.

Within those names, the theorems cover a key the selector also sets (`div#a`
with `{id: "z"}`: removing the key restores `id="a"`), a key respelled in
another case between patches (the update removes before it writes), and
namespaced keys, on HTML elements.

## How the proof is split

| File | What it proves |
| --- | --- |
| `Dom.lean` | The DOM model: nodes with kind, attributes, children and parent; `createElement` and the attribute calls (`setAttribute` and `removeAttribute` lowercase the name, the namespaced ones do not), `insertBefore` (with the DOM's own "move if already attached" rule), `removeChild`, `setText`. A misplaced `insertBefore` or `removeChild` sets `ok := false`, standing in for a DOM exception. |
| `Spec.lean` | What "correct" means: `VNode.render`, `Shows`, `Mirrors`, `HeapWF`, `PPre`, `Valid`, and the input restriction `VNode.WF`. |
| `Proofs/Basic.lean` | Each DOM operation keeps the heap well formed; exact effect of `insertBefore` and `removeChild`. |
| `Proofs/Attrs.lean` | The selector's `id`/`class` and the Attributes module: after `create` the element's attributes are `renderAttrs`; after `update` (removals, which fall back to the selector's value, then writes) they are exactly the new ones. |
| `Proofs/Create.lean` | `createElm` builds a fresh subtree that shows `v.render` and is a `Valid` input to `patch`. |
| `Proofs/PlaceList.lean` | `placeAroundAnchors`, the reordering loop used when an unkeyed child matched after the common prefix, on plain lists: after it, the reused and new children appear in the new order. This is the hardest lemma. |
| `Proofs/Place.lean` | The same loop on the DOM heap. |
| `Proofs/Children.lean` | Removing unused old children; appending new ones; node identity among siblings. |
| `Proofs/PlaceFewest.lean` | `placeWithFewestMoves`: `longestIncreasingRun` returns indexes whose old positions increase, so keeping those children and moving the rest puts all of them in the new order. |
| `Proofs/Patch.lean` | The child-matching fold: each new child reuses at most one old child (by position if unkeyed, by key otherwise), and the old children not reused are removed. Also the three ways `updateChildren` then places the children: append the new ones when every old child matched in place, `placeAroundAnchors`, or `placeWithFewestMoves`. |
| `Proofs/PatchVnode.lean` | `patchVnode` and the matching fold, by mutual induction. |
| `Proofs/Main.lean` | `patch` (including replacing a node with an incompatible one) and `diff_eq_recreate`. |
| `Axioms.lean` | Fails the build if a main theorem depends on `sorry` or a non-standard axiom. |

## What is not modeled

The proof says nothing about these parts of the library:

* user hooks (`init`, `create`, `insert`, `prepatch`, `update`, `remove`, `destroy`, `post`) and delayed removal
* thunks, SVG (`createElementNS`), and fragments. The model's elements are
  all HTML elements, whose attribute names the DOM lowercases; on an SVG
  element it does not, and the Attributes module compares a dropped key with
  the selector's `id` and `class` without lowercasing it. The proof does not
  cover that branch.
* hydration (`toVNode`). An attribute parsed from HTML markup has no
  namespace even when its name has a prefix, so dropping the key `xml:lang`
  from a vnode hydrated from `<div xml:lang="fr">` leaves the attribute.
* exceptions on names. `createElement` and `setAttribute` throw
  `InvalidCharacterError` on an invalid name, such as the empty tag that the
  selector `#a` gives or a key with a space in it. The model accepts every
  name, so `WF` requires `SafeName` for tags and `AttrName` for keys: a
  conservative subset (an ASCII letter, then ASCII letters, digits, `-`, `_`
  or `.`, after one of the three prefixes for a namespaced key) that browsers
  accept under both the current DOM standard and its older XML `Name` rule.
* namespaces as such. The DOM keys a namespaced attribute by namespace and
  local name; the model keys it by its qualified name, which is the same
  thing because the Attributes module ties each prefix to one namespace. It
  cannot hold a namespaced attribute and a plain one with the same qualified
  name (`xlink:href` and `XLINK:href` lowercased), which `WF` keeps apart.
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
so the normal test suite skips it. CI's `Formal` job runs `lake build` and
`conformance.sh` on every push and pull request.
