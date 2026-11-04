# Formal verification of `patch`

This directory proves, in Lean 4, that snabbdom's diff is correct:
**patching an old tree into a new vnode leaves the same DOM that rendering the
new vnode from scratch would.**

It has two parts:

1. **A proof about a model.** `Snabbdom/Model.lean` transcribes `init.scala`
   (`createElm`, `patchVnode`, `updateChildren`, `patch`) and the Attributes
   module into Lean, on top of a small DOM (`Snabbdom/Dom.lean`). The theorems
   in `Snabbdom/Proofs/` are about that model. They have no `sorry` and use only
   Lean's three standard axioms (`#print axioms Snabbdom.diff_eq_recreate`).
2. **A bridge from the model to the Scala code.** Lean cannot read Scala, so
   `conformance.sh` runs the real library in headless Chrome on 10,000 random
   `(old, new)` pairs. A recording `DomApi` logs every DOM call. The Lean model
   then replays each case and must produce the same calls in the same order
   and the same final DOM. Last run: 10,000 cases, about 140,000 DOM operations,
   0 mismatches.

So the guarantee is: the algorithm, as modeled, is proved correct for every
input; and the model matches the Scala implementation on every input tested.
The second half is testing, not proof. A Scala behavior that the generator
never exercises could still differ from the model.

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
    Valid (patch old v d).2 (patch old v d).1 ∧            -- the DOM is still well formed, no DOM exception
    (patch old v d).1.toVNode = v ∧                         -- the returned tree describes v
    Shows (patch old v d).2 (patch old v d).1.node v.render ∧
    (∀ i, i < d.next → i ∉ old.ids → d.parentNode old.node ≠ some i →
      (patch old v d).2.nodes i = d.nodes i) ∧              -- nothing outside old's subtree changed...
    (∀ p px, d.parentNode old.node = some p → d.nodes p = some px →
      (patch old v d).2.nodes p =                           -- ...except that the parent now holds
        some { px with children := replaceIn old.node (patch old v d).1.node px.children }) ∧
    (d.parentNode old.node = none → ...)                    -- a detached root stays detached
```

`Valid d old` is what `patch` expects of its input: the DOM is a well-formed
forest (`HeapWF`), no DOM exception has happened yet (`ok`), and `old` agrees
with the DOM node by node (`Repr`). `v.WF` says attribute keys are unique
(they come from a Scala `Map`).

`createElm_shows` (`Proofs/Create.lean`) is the "from scratch" half:
`createElm v` builds a subtree that shows `v.render`.

## How the proof is split

| File | What it proves |
| --- | --- |
| `Dom.lean` | The DOM model: nodes with kind, attributes, children and parent; `insertBefore` (with the DOM's own "move if already attached" rule), `removeChild`, `setText`, attribute calls. Invalid calls set `ok := false`, standing in for a DOM exception. |
| `Spec.lean` | What "correct" means: `VNode.render`, `Shows`, `Repr`, `HeapWF`, `Valid`. |
| `Proofs/Basic.lean` | Each DOM operation keeps the heap well formed; exact effect of `insertBefore` and `removeChild`. |
| `Proofs/Attrs.lean` | The Attributes module: after `update`, the element's attributes are exactly the new ones. |
| `Proofs/Create.lean` | `createElm` builds a fresh subtree that shows `v.render`. |
| `Proofs/PlaceList.lean` | The child reordering loop on plain lists: after it, the reused and new children appear in the new order. This is the hardest lemma. |
| `Proofs/Place.lean` | The same loop on the DOM heap. |
| `Proofs/Children.lean` | Removing unused old children; appending new ones; node identity among siblings. |
| `Proofs/Patch.lean` | The child-matching fold: each new child reuses at most one old child (by position if unkeyed, by key otherwise), and the old children not reused are removed. |
| `Proofs/PatchVnode.lean` | `patchVnode` and the matching fold, by mutual induction. |
| `Proofs/Main.lean` | `patch` (including replacing a node with an incompatible one) and `diff_eq_recreate`. |

## What is not modeled

The proof says nothing about these parts of the library:

* user hooks (`init`, `create`, `insert`, `prepatch`, `update`, `remove`, `destroy`, `post`) and delayed removal
* thunks, SVG namespaces (`createElementNS`, `setAttributeNS`), and fragments
* the Props, Class, Style, Dataset and EventListeners modules (only Attributes is modeled)
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
