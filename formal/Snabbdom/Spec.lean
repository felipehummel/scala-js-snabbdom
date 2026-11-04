/-
What "the DOM is correct" means.

* `VNode.render v` is the DOM tree a vnode should produce, ignoring node
  identity: kind, selector, attributes and children, recursively. Rendering
  from scratch (`createElm`) and patching must both produce it.
* `Shows d n t`: in DOM `d`, the subtree rooted at node `n` is exactly `t`.
* `Repr d p`: the DOM agrees with a `PatchedVNode` `p`, node by node. This is
  what `patch` assumes about its `old` argument and guarantees about its result.
* `HeapWF d`: the DOM is a well-formed forest (parent pointers and child lists
  agree, child lists have no duplicates, ids are below `next`).
-/
import Snabbdom.Model

namespace Snabbdom

/-! ## Expected DOM -/

inductive DTree where
  | text (s : String)
  | comment (s : String)
  | elem (sel : String) (attrs : String → Option String) (children : List DTree)

def AttrVal.render : AttrVal → Option String
  | .str s => some s
  | .bool true => some ""
  | .bool false => none

def renderAttrs (a : Attrs) : String → Option String :=
  fun k => (a.lookup k).bind AttrVal.render

mutual
def VNode.render : VNode → DTree
  | .text s => .text s
  | .comment s => .comment s
  | .elem sel d ch => .elem sel (renderAttrs d.attrs) (VNode.renders ch)
def VNode.renders : List VNode → List DTree
  | [] => []
  | v :: vs => v.render :: VNode.renders vs
end

-- Attribute keys are unique (they come from a Scala `Map`).
mutual
def VNode.WF : VNode → Prop
  | .elem _ d ch => (d.attrs.map (·.1)).Nodup ∧ VNode.WFs ch
  | _ => True
def VNode.WFs : List VNode → Prop
  | [] => True
  | v :: vs => v.WF ∧ VNode.WFs vs
end

/-! ## Reading the DOM -/

mutual
def Shows (d : Dom) (n : NodeId) : DTree → Prop
  | .text s => ∃ x, d.nodes n = some x ∧ x.kind = .text s ∧ x.children = []
  | .comment s => ∃ x, d.nodes n = some x ∧ x.kind = .comment s ∧ x.children = []
  | .elem sel a ts =>
    ∃ x, d.nodes n = some x ∧ x.kind = .elem sel ∧ x.attrs = a ∧ ShowsList d x.children ts
def ShowsList (d : Dom) : List NodeId → List DTree → Prop
  | [], [] => True
  | n :: ns, t :: ts => Shows d n t ∧ ShowsList d ns ts
  | _, _ => False
end

/-! ## Patched vnodes and the DOM -/

mutual
def Repr (d : Dom) : PNode → Prop
  | .text s n => ∃ x, d.nodes n = some x ∧ x.kind = .text s ∧ x.children = []
  | .comment s n => ∃ x, d.nodes n = some x ∧ x.kind = .comment s ∧ x.children = []
  | .elem sel data ch n =>
    ∃ x, d.nodes n = some x ∧ x.kind = .elem sel ∧ x.attrs = renderAttrs data.attrs ∧
      x.children = ch.map PNode.node ∧ ReprList d ch
def ReprList (d : Dom) : List PNode → Prop
  | [] => True
  | p :: ps => Repr d p ∧ ReprList d ps
end

-- All DOM node ids in a patched tree.
mutual
def PNode.ids : PNode → List NodeId
  | .text _ n => [n]
  | .comment _ n => [n]
  | .elem _ _ ch n => n :: PNode.idsList ch
def PNode.idsList : List PNode → List NodeId
  | [] => []
  | p :: ps => p.ids ++ PNode.idsList ps
end

structure HeapWF (d : Dom) : Prop where
  bound : ∀ i x, d.nodes i = some x → i < d.next
  child_parent : ∀ p px c, d.nodes p = some px → c ∈ px.children →
    ∃ cx, d.nodes c = some cx ∧ cx.parent = some p
  parent_child : ∀ c cx p, d.nodes c = some cx → cx.parent = some p →
    ∃ px, d.nodes p = some px ∧ c ∈ px.children
  nodup : ∀ p px, d.nodes p = some px → px.children.Nodup

/-- What `patch` needs from its `old` argument, and gives back for its result. -/
structure Valid (d : Dom) (p : PNode) : Prop where
  heap : HeapWF d
  ok : d.ok = true
  repr : Repr d p
  ids_nodup : p.ids.Nodup
  ids_bound : ∀ i ∈ p.ids, i < d.next
  wf : p.toVNode.WF

end Snabbdom
