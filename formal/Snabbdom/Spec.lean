/-
What "the DOM is correct" means. `VNode.render` ignores node identity on
purpose: patching reuses nodes and rendering from scratch makes new ones, so
the two can only agree on kind, tag, attributes and children.
-/
import Snabbdom.Model

namespace Snabbdom

/-- An element's attributes as read by qualified name: each one's namespace and
value. -/
abbrev AttrView := String → Option (Option String × String)

inductive DTree where
  | text (s : String)
  | comment (s : String)
  | elem (tag : String) (attrs : AttrView) (children : List DTree)

/-- The attribute list read by qualified name. -/
def attrView (l : List Attr) : AttrView :=
  fun q => (l.find? (·.qname == q)).map fun a => (a.ns, a.value)

/-- `l` holds one attribute per qualified name and reads as `a`. -/
def AttrsShow (l : List Attr) (a : AttrView) : Prop :=
  (l.map Attr.qname).Nodup ∧ attrView l = a

/-- The attribute is in the namespace `namespaceOf` reads from its qualified
name, with that namespace's prefix, as the Attributes module writes them. -/
def Attr.Canon (a : Attr) : Prop :=
  match a.ns with
  | none => a.pfx = none ∧ namespaceOf a.localName = none
  | some ns => a.pfx = some (nsPrefix ns) ∧ namespaceOf a.qname = some ns

/-- What `Mirrors` asks of an element's attributes: `AttrsShow`, and each
attribute `Canon`. -/
def AttrsMirror (l : List Attr) (a : AttrView) : Prop :=
  AttrsShow l a ∧ ∀ x ∈ l, x.Canon

def AttrVal.render : AttrVal → Option String
  | .str s => some s
  | .bool true => some ""
  | .bool false => none

/-- The entry that sets the attribute named `j`, through whichever key names it. -/
def Attrs.get (a : Attrs) (j : String) : Option (String × AttrVal) :=
  a.find? (fun kv => attrName kv.1 == j)

/-- The attributes `createElm` leaves: the vnode's own, in the namespace its
key names, over the selector's. -/
def renderAttrs (sel : String) (a : Attrs) : AttrView :=
  fun k => match a.get k with
    | some kv => kv.2.render.map (namespaceOf kv.1, ·)
    | none => ((Selector.parse sel).attr k).map (none, ·)

mutual
def VNode.render : VNode → DTree
  | .text s => .text s
  | .comment s => .comment s
  | .elem sel d ch =>
    .elem (asciiLower (Selector.parse sel).tag) (renderAttrs sel d.attrs) (VNode.renders ch)
def VNode.renders : List VNode → List DTree
  | [] => []
  | v :: vs => v.render :: VNode.renders vs
end

/-- A conservative subset of the names that `createElement` and `setAttribute`
accept without `InvalidCharacterError`, under both the current DOM standard and
its older XML `Name` rule: an ASCII letter, then ASCII letters, digits, `-`,
`_` or `.`. -/
def SafeName (s : String) : Prop :=
  match s.toList with
  | c :: cs => c.isAlpha ∧ ∀ c ∈ cs, c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = '.'
  | [] => False

/-- The keys the Attributes module writes without a DOM exception: a `SafeName`,
or `xml:`, `xmlns:` or `xlink:` then a `SafeName`, which `setAttributeNS`
accepts in the namespace that prefix names. -/
def AttrName (k : String) : Prop :=
  SafeName k ∨ ∃ p ∈ ["xml", "xmlns", "xlink"], ∃ l, SafeName l ∧ k = p ++ ":" ++ l

/-- One key per attribute name: a Scala `Map` holding both `title` and `TITLE`
sets one attribute twice, and which write wins depends on its iteration order. -/
def AttrsWF (a : Attrs) : Prop :=
  (a.map (attrName ·.1)).Nodup ∧ ∀ kv ∈ a, AttrName kv.1

mutual
/-- Sufficient, not necessary: a per-vnode condition, so that it carries over
from one patch to the next. -/
def VNode.WF : VNode → Prop
  | .elem sel d ch => SafeName (Selector.parse sel).tag ∧ AttrsWF d.attrs ∧ VNode.WFs ch
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
    ∃ x, d.nodes n = some x ∧ x.kind = .elem tag ∧ AttrsShow x.attrs a ∧ ShowsList d x.children ts
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
    ∃ x, d.nodes n = some x ∧ x.kind = .elem (asciiLower (Selector.parse sel).tag) ∧
      AttrsMirror x.attrs (renderAttrs sel data.attrs) ∧
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

/-- `p` agrees with the well-formed DOM `d`: what `patchVnode` assumes of its
`old` argument. -/
structure PPre (d : Dom) (p : PNode) : Prop where
  wf : HeapWF d
  mirrors : Mirrors d p
  ids_nodup : p.ids.Nodup
  ids_lt : ∀ i ∈ p.ids, i < d.next
  vnode_wf : p.toVNode.WF

/-- What `patch` expects of its input: `PPre`, and no DOM exception so far. -/
structure Valid (d : Dom) (p : PNode) : Prop extends PPre d p where
  ok : d.ok = true

end Snabbdom
