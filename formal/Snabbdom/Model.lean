/-
A transcription of `snabbdom/src/main/scala/snabbdom/init.scala` (with the
`Attributes` module) into Lean.

Each definition mirrors the Scala function of the same name; comments point at
the Scala lines. Effects on the DOM go through `Dom` (see `Dom.lean`) in the
same order as the Scala code calls `DomApi`.

Not modelled: user hooks (`data.hook`), thunks, namespaces, event listeners,
and the Props/Classes/Styles/Dataset modules. None of the standard modules has a
`remove` hook, so removal is immediate, as below.
-/
import Snabbdom.Dom

namespace Snabbdom

/-! ## Virtual nodes -/

inductive AttrVal where
  | str (s : String)
  | bool (b : Bool)
  deriving DecidableEq, Repr

abbrev Attrs := List (String × AttrVal)

structure Data where
  key : Option String := none
  is : Option String := none
  attrs : Attrs := []
  deriving DecidableEq, Repr

inductive VNode where
  | text (s : String)
  | comment (s : String)
  | elem (sel : String) (data : Data) (children : List VNode)
  deriving Repr, Inhabited

mutual
def VNode.decEq : (a b : VNode) → Decidable (a = b)
  | .text s, .text t => if h : s = t then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .comment s, .comment t => if h : s = t then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .elem s d c, .elem s' d' c' =>
    if h1 : s = s' then
      if h2 : d = d' then
        match VNode.decEqList c c' with
        | isTrue h3 => isTrue (by subst h1 h2 h3; rfl)
        | isFalse h3 => isFalse (by intro e; cases e; exact h3 rfl)
      else isFalse (by intro e; cases e; exact h2 rfl)
    else isFalse (by intro e; cases e; exact h1 rfl)
  | .text _, .comment _ | .text _, .elem .. | .comment _, .text _ | .comment _, .elem ..
  | .elem .., .text _ | .elem .., .comment _ => isFalse (by intro e; cases e)
def VNode.decEqList : (a b : List VNode) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match VNode.decEq x y, VNode.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq VNode := VNode.decEq

def VNode.key : VNode → Option String
  | .elem _ d _ => d.key
  | _ => none

/-- `PatchedVNode`: a vnode together with the DOM node it was rendered into. -/
inductive PNode where
  | text (s : String) (node : NodeId)
  | comment (s : String) (node : NodeId)
  | elem (sel : String) (data : Data) (children : List PNode) (node : NodeId)
  deriving Repr, Inhabited

def PNode.node : PNode → NodeId
  | .text _ n | .comment _ n | .elem _ _ _ n => n

def PNode.key : PNode → Option String
  | .elem _ d _ _ => d.key
  | _ => none

mutual
def PNode.toVNode : PNode → VNode
  | .text s _ => .text s
  | .comment s _ => .comment s
  | .elem sel d ch _ => .elem sel d (PNode.toVNodes ch)
def PNode.toVNodes : List PNode → List VNode
  | [] => []
  | p :: ps => p.toVNode :: PNode.toVNodes ps
end

/-- init.scala:466 -/
def sameVnode : PNode → VNode → Bool
  | .text _ _, .text _ => true
  | .elem s1 d1 _ _, .elem s2 d2 _ => d1.key == d2.key && d1.is == d2.is && s1 == s2
  | _, _ => false

/-! ## The Attributes module (modules/Attributes.scala) -/

def applyAttr (d : Dom) (n : NodeId) (k : String) : AttrVal → Dom
  | .bool true => d.setAttr n k ""
  | .bool false => d.removeAttr n k
  | .str s => d.setAttr n k s

def setAttrs (n : NodeId) (attrs : Attrs) (d : Dom) : Dom :=
  attrs.foldl (fun d kv => applyAttr d n kv.1 kv.2) d

def updateAttrs (n : NodeId) (old new : Attrs) (d : Dom) : Dom :=
  let d := new.foldl
    (fun d kv => if old.lookup kv.1 ≠ some kv.2 then applyAttr d n kv.1 kv.2 else d) d
  old.foldl (fun d kv => if (new.lookup kv.1).isNone then d.removeAttr n kv.1 else d) d

/-- `cbs.create` -/
def moduleCreate (p : PNode) (d : Dom) : Dom :=
  match p with
  | .elem _ data _ n => if data.attrs ≠ [] then setAttrs n data.attrs d else d
  | _ => d

/-- `cbs.update` -/
def moduleUpdate (old : PNode) (v : VNode) (d : Dom) : Dom :=
  match old, v with
  | .elem _ a _ n, .elem _ b _ => if a.attrs ≠ b.attrs then updateAttrs n a.attrs b.attrs d else d
  | _, _ => d

/-! ## createElm (init.scala:110) -/

def appendAll (n : NodeId) : List PNode → Dom → Dom
  | [], d => d
  | c :: cs, d => appendAll n cs (d.appendChild n c.node)

mutual
def createElm : VNode → Dom → PNode × Dom
  | .comment s, d =>
    let (n, d) := d.createComment s
    (.comment s n, d)
  | .text s, d =>
    let (n, d) := d.createText s
    (.text s n, d)
  | .elem sel data ch, d =>
    let (n, d) := d.createElement sel
    let (pch, d) := createElms ch d
    let p := PNode.elem sel data pch n
    let d := moduleCreate p d
    let d := appendAll n pch d
    (p, d)
def createElms : List VNode → Dom → List PNode × Dom
  | [], d => ([], d)
  | v :: vs, d =>
    let (p, d) := createElm v d
    let (ps, d) := createElms vs d
    (p :: ps, d)
end

/-! ## removeAllVnodes (init.scala:184) -/

def removeAllVnodes (parentElm : NodeId) : List PNode → Dom → Dom
  | [], d => d
  | .elem _ _ _ n :: rest, d =>
    -- the remove callback removes the node from its *current* parent
    let d := match d.parentNode n with
      | some p => d.removeChild p n
      | none => d
    removeAllVnodes parentElm rest d
  | o :: rest, d => removeAllVnodes parentElm rest (d.removeChild parentElm o.node)

/-! ## updateChildren (init.scala:203) -/

inductive Placement where
  /-- unkeyed match, never moved -/
  | anchored (child : PNode)
  /-- keyed match or newly created -/
  | movable (child : PNode)
  deriving Repr, Inhabited

def Placement.child : Placement → PNode
  | .anchored c | .movable c => c

/-- `oldByKey`: old children with key `k`, in order. -/
def keyedOld (oldCh : List PNode) (k : String) : List PNode :=
  oldCh.filter (·.key == some k)

/-- init.scala:248. The `nextSibling` loop, written as a search over the
siblings from `cursor` on. -/
def nextReconciledNode (d : Dom) (reconciled : List NodeId) : Option NodeId → Option NodeId
  | none => none
  | some o => (d.siblingsFrom o).find? (· ∈ reconciled)

/-- init.scala:257 -/
def place (parentElm : NodeId) (reconciled : List NodeId) :
    List Placement → Option NodeId → Dom → Dom
  | [], _, d => d
  | .anchored c :: rest, _, d => place parentElm reconciled rest (d.nextSibling c.node) d
  | .movable c :: rest, cursor, d =>
    let reference := nextReconciledNode d reconciled cursor
    if reference = some c.node then
      place parentElm reconciled rest (d.nextSibling c.node) d
    else
      place parentElm reconciled rest reference (d.insertBefore parentElm c.node reference)

/-- init.scala:245-279, after the matching fold. -/
def finishChildren (parentElm : NodeId) (oldCh : List PNode) (pls : List Placement)
    (d : Dom) : List PNode × Dom :=
  let reconciled := pls.map (·.child.node)
  let d := place parentElm reconciled pls (oldCh.head?.map (·.node)) d
  let d := removeAllVnodes parentElm (oldCh.filter (fun o => o.node ∉ reconciled)) d
  (pls.map (·.child), d)

/-- init.scala:354, `case (Nil, ch @ _ :: _)` -/
def createAndInsert (elm : NodeId) : List VNode → Dom → List PNode × Dom
  | [], d => ([], d)
  | v :: vs, d =>
    let (p, d) := createElm v d
    let d := d.insertBefore elm p.node none
    let (ps, d) := createAndInsert elm vs d
    (p :: ps, d)

/-! ## patchVnode (init.scala:283) and the matching fold (init.scala:215) -/

/-- One step of the `foldLeft` over the new children (init.scala:215): find
the old child that `v` reuses, or create a fresh one. `pv o d` patches `o`
into `v`. `pos` is the index of `v`; `byKey` holds the old keyed children not
claimed yet. -/
def matchOne (oldCh : List PNode) (byKey : String → List PNode) (pos : Nat) (v : VNode)
    (pv : PNode → Dom → PNode × Dom) (d : Dom) : Placement × (String → List PNode) × Dom :=
  let created : Placement × (String → List PNode) × Dom :=
    let (c, d) := createElm v d
    (.movable c, byKey, d)
  match v.key with
  | none =>
    match oldCh[pos]? with
    | some o =>
      if sameVnode o v then
        let (c, d) := pv o d
        (.anchored c, byKey, d)
      else created
    | none => created
  | some k =>
    match (byKey k).span (fun o => !sameVnode o v) with
    | (skipped, o :: rest) =>
      let (c, d) := pv o d
      (.movable c, fun j => if j = k then skipped ++ rest else byKey j, d)
    | (_, []) => created

mutual
def patchVnode (old : PNode) (v : VNode) (d : Dom) : PNode × Dom :=
  if v = old.toVNode then (old, d)
  else
    let d := moduleUpdate old v d
    match old, v with
    | .comment os n, .comment s => (.comment s n, if os ≠ s then d.setText n s else d)
    | .text os n, .text s => (.text s n, if os ≠ s then d.setText n s else d)
    | .elem _ _ oldCh elm, .elem sel data ch =>
      match oldCh, ch with
      | _ :: _, c :: cs =>
        if PNode.toVNodes oldCh ≠ c :: cs then
          let (pls, d) := matchChildren oldCh (keyedOld oldCh) 0 (c :: cs) d
          let (pch, d) := finishChildren elm oldCh pls d
          (.elem sel data pch elm, d)
        else (.elem sel data oldCh elm, d)
      | [], c :: cs =>
        let (pch, d) := createAndInsert elm (c :: cs) d
        (.elem sel data pch elm, d)
      | _ :: _, [] => (.elem sel data [] elm, removeAllVnodes elm oldCh d)
      | [], [] => (.elem sel data [] elm, d)
    | _, _ => (old, d.fail) -- "trying to patch incompatible nodes"

/-- The `foldLeft` over the new children. -/
def matchChildren (oldCh : List PNode) (byKey : String → List PNode) (pos : Nat) :
    List VNode → Dom → List Placement × Dom
  | [], d => ([], d)
  | v :: vs, d =>
    let (pl, byKey', d) := matchOne oldCh byKey pos v (fun o d => patchVnode o v d) d
    let (pls, d) := matchChildren oldCh byKey' (pos + 1) vs d
    (pl :: pls, d)
end

/-! ## patch (init.scala:410) -/

def patch (old : PNode) (v : VNode) (d : Dom) : PNode × Dom :=
  if sameVnode old v then patchVnode old v d
  else
    let parent := d.parentNode old.node
    let (nv, d) := createElm v d
    match parent with
    | some p =>
      let d := d.insertBefore p nv.node (d.nextSibling old.node)
      (nv, removeAllVnodes p [old] d)
    | none => (nv, d)

end Snabbdom
