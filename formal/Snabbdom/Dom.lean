/-
The DOM operations snabbdom performs, on a heap of nodes in an HTML document,
following the DOM standard. Where a browser would throw `NotFoundError` (from
`insertBefore` or `removeChild`), the model sets `ok := false` instead, and the
proofs show that never happens. The model does not check names, so it misses
the `InvalidCharacterError` that `createElement` and the attribute calls throw
on some; `VNode.WF` keeps the theorems away from those names (see "What is not
modeled" in README.md).

`trace` records the structural calls in the form the conformance check compares
with Scala's `DomApi`. Attribute writes are not in it: the Scala code makes them
on the element directly, so the check compares them through the final DOM.
-/

namespace Snabbdom

notation "NodeId" => Nat

inductive Kind where
  | text (s : String)
  | comment (s : String)
  | elem (tag : String)
  deriving DecidableEq, Repr

structure DomNode where
  kind : Kind
  attrs : String → Option String := fun _ => none
  children : List NodeId := []
  parent : Option NodeId := none

inductive Op where
  | createElement (n : NodeId) (tag : String)
  | createText (n : NodeId) (s : String)
  | createComment (n : NodeId) (s : String)
  | insertBefore (p n : NodeId) (ref : Option NodeId)
  | appendChild (p n : NodeId)
  | removeChild (p n : NodeId)
  | setText (n : NodeId) (s : String)
  deriving DecidableEq, Repr

structure Dom where
  nodes : NodeId → Option DomNode
  next : NodeId
  /-- `false` once an operation would have thrown in a browser. -/
  ok : Bool := true
  trace : Array Op := #[]

def insertAt (n : NodeId) : Option NodeId → List NodeId → List NodeId
  | none, l => l ++ [n]
  | some _, [] => [n]
  | some r, x :: xs => if x = r then n :: x :: xs else x :: insertAt n (some r) xs

def after (n : NodeId) : List NodeId → Option NodeId
  | [] => none
  | x :: xs => if x = n then xs.head? else after n xs

/-- In an HTML document, `createElement`, `setAttribute` and `removeAttribute`
lowercase the name they are given (ASCII only, which is what `Char.toLower`
does). -/
def asciiLower (k : String) : String := String.ofList (k.toList.map Char.toLower)

namespace Dom

def empty : Dom := { nodes := fun _ => none, next := 0 }

def get (d : Dom) (n : NodeId) : Option DomNode := d.nodes n

def modify (d : Dom) (n : NodeId) (f : DomNode → DomNode) : Dom :=
  { d with nodes := fun m => if m = n then (d.nodes m).map f else d.nodes m }

def log (d : Dom) (op : Op) : Dom := { d with trace := d.trace.push op }

def fail (d : Dom) : Dom := { d with ok := false }

def alloc (d : Dom) (k : Kind) : NodeId × Dom :=
  let n := d.next
  (n, { d with nodes := fun m => if m = n then some { kind := k } else d.nodes m,
               next := n + 1 })

def createElement (d : Dom) (tag : String) : NodeId × Dom :=
  let (n, d) := d.alloc (.elem (asciiLower tag))
  (n, d.log (.createElement n tag))

def createText (d : Dom) (s : String) : NodeId × Dom :=
  let (n, d) := d.alloc (.text s)
  (n, d.log (.createText n s))

def createComment (d : Dom) (s : String) : NodeId × Dom :=
  let (n, d) := d.alloc (.comment s)
  (n, d.log (.createComment n s))

def parentNode (d : Dom) (n : NodeId) : Option NodeId :=
  (d.get n).bind (·.parent)

def nextSibling (d : Dom) (n : NodeId) : Option NodeId :=
  match d.parentNode n with
  | none => none
  | some p =>
    match d.get p with
    | none => none
    | some px => after n px.children

def siblingsFrom (d : Dom) (n : NodeId) : List NodeId :=
  match d.parentNode n with
  | none => [n]
  | some p =>
    match d.get p with
    | none => [n]
    | some px => px.children.dropWhile (· ≠ n)

def detach (d : Dom) (n : NodeId) : Dom :=
  match d.parentNode n with
  | none => d
  | some q =>
    (d.modify q fun x => { x with children := x.children.erase n }).modify n
      fun x => { x with parent := none }

/-- `insertBefore` throws `NotFoundError` unless `ref` is a child of the parent. -/
def refValid (children : List NodeId) : Option NodeId → Bool
  | none => true
  | some r => decide (r ∈ children)

/-- The DOM standard's "pre-insert", shared by `insertBefore` and `appendChild`. -/
def preInsert (d : Dom) (p n : NodeId) (ref : Option NodeId) : Dom :=
  match d.get p, d.get n with
  | some px, some _ =>
    if !refValid px.children ref then d.fail
    else
      -- "If child is node, set child to node's next sibling."
      let ref := if ref = some n then d.nextSibling n else ref
      let d := d.detach n
      (d.modify p fun x => { x with children := insertAt n ref x.children }).modify n
        fun x => { x with parent := some p }
  | _, _ => d.fail

def insertBefore (d : Dom) (p n : NodeId) (ref : Option NodeId) : Dom :=
  (d.log (.insertBefore p n ref)).preInsert p n ref

def appendChild (d : Dom) (p n : NodeId) : Dom :=
  (d.log (.appendChild p n)).preInsert p n none

def removeChild (d : Dom) (p c : NodeId) : Dom :=
  let d := d.log (.removeChild p c)
  match d.get p with
  | some px =>
    if c ∈ px.children then
      (d.modify p fun x => { x with children := x.children.erase c }).modify c
        fun x => { x with parent := none }
    else d.fail
  | none => d.fail

def setText (d : Dom) (n : NodeId) (s : String) : Dom :=
  let d := d.log (.setText n s)
  match d.get n with
  | some { kind := .text _, .. } => d.modify n fun x => { x with kind := .text s }
  | some { kind := .comment _, .. } => d.modify n fun x => { x with kind := .comment s }
  | _ => d.fail

def setAttr (d : Dom) (n : NodeId) (k v : String) : Dom :=
  d.modify n fun x => { x with attrs := fun j => if j = asciiLower k then some v else x.attrs j }

def removeAttr (d : Dom) (n : NodeId) (k : String) : Dom :=
  d.modify n fun x => { x with attrs := fun j => if j = asciiLower k then none else x.attrs j }

/-- `setAttributeNS`, which does not lowercase. The model keys a namespaced
attribute by its qualified name `k`; the DOM keys it by namespace and local
name, which is the same thing as long as each prefix comes with one namespace,
as in the Attributes module. -/
def setAttrNS (d : Dom) (n : NodeId) (k v : String) : Dom :=
  d.modify n fun x => { x with attrs := fun j => if j = k then some v else x.attrs j }

/-- `removeAttributeNS`, with the local name of `k`. -/
def removeAttrNS (d : Dom) (n : NodeId) (k : String) : Dom :=
  d.modify n fun x => { x with attrs := fun j => if j = k then none else x.attrs j }

end Dom

end Snabbdom
