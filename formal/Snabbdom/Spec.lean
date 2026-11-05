/-
What "the DOM is correct" means. `VNode.render` ignores node identity on
purpose: patching reuses nodes and rendering from scratch makes new ones, so
the two can only agree on kind, tag, attributes and children.
-/
import Snabbdom.Model

namespace Snabbdom

inductive DTree where
  | text (s : String)
  | comment (s : String)
  | elem (tag : String) (attrs : String → Option String) (children : List DTree)

def AttrVal.render : AttrVal → Option String
  | .str s => some s
  | .bool true => some ""
  | .bool false => none

/-- The attributes `createElm` leaves: the vnode's own over the selector's. -/
def renderAttrs (sel : String) (a : Attrs) : String → Option String :=
  fun k => match a.lookup k with
    | some v => v.render
    | none => (Selector.parse sel).attr k

mutual
def VNode.render : VNode → DTree
  | .text s => .text s
  | .comment s => .comment s
  | .elem sel d ch => .elem (Selector.parse sel).tag (renderAttrs sel d.attrs) (VNode.renders ch)
def VNode.renders : List VNode → List DTree
  | [] => []
  | v :: vs => v.render :: VNode.renders vs
end

/-- Keys are unique because they come from a Scala `Map`. The other two
clauses restrict the theorem to where the library has the property; the
README gives a counterexample for each. -/
def AttrsWF (sel : String) (a : Attrs) : Prop :=
  (a.map (·.1)).Nodup ∧
    ∀ kv ∈ a, attrName kv.1 = kv.1 ∧ (Selector.parse sel).attr kv.1 = none

mutual
def VNode.WF : VNode → Prop
  | .elem sel d ch => AttrsWF sel d.attrs ∧ VNode.WFs ch
  | _ => True
def VNode.WFs : List VNode → Prop
  | [] => True
  | v :: vs => v.WF ∧ VNode.WFs vs
end

mutual
/-- In DOM `d`, the subtree rooted at `n` is exactly `t`. -/
def Shows (d : Dom) (n : NodeId) : DTree → Prop
  | .text s => ∃ x, d.nodes n = some x ∧ x.kind = .text s ∧ x.children = []
  | .comment s => ∃ x, d.nodes n = some x ∧ x.kind = .comment s ∧ x.children = []
  | .elem tag a ts =>
    ∃ x, d.nodes n = some x ∧ x.kind = .elem tag ∧ x.attrs = a ∧ ShowsList d x.children ts
def ShowsList (d : Dom) : List NodeId → List DTree → Prop
  | [], [] => True
  | n :: ns, t :: ts => Shows d n t ∧ ShowsList d ns ts
  | _, _ => False
end

mutual
/-- The DOM agrees with a patched vnode node by node: what `patch` assumes of
`old` and guarantees of its result. -/
def Mirrors (d : Dom) : PNode → Prop
  | .text s n => ∃ x, d.nodes n = some x ∧ x.kind = .text s ∧ x.children = []
  | .comment s n => ∃ x, d.nodes n = some x ∧ x.kind = .comment s ∧ x.children = []
  | .elem sel data ch n =>
    ∃ x, d.nodes n = some x ∧ x.kind = .elem (Selector.parse sel).tag ∧
      x.attrs = renderAttrs sel data.attrs ∧
      x.children = ch.map PNode.node ∧ MirrorsList d ch
def MirrorsList (d : Dom) : List PNode → Prop
  | [] => True
  | p :: ps => Mirrors d p ∧ MirrorsList d ps
end

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

structure Valid (d : Dom) (p : PNode) : Prop where
  heap : HeapWF d
  ok : d.ok = true
  mirrors : Mirrors d p
  ids_nodup : p.ids.Nodup
  ids_bound : ∀ i ∈ p.ids, i < d.next
  wf : p.toVNode.WF

end Snabbdom
