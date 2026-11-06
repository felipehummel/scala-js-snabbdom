/-
A transcription of `snabbdom/src/main/scala/snabbdom/init.scala` and
`modules/Attributes.scala`. Each definition mirrors a Scala function or match
case, named in its name or docstring, and makes its DOM calls in the same order. What is left out is listed in
`formal/README.md`. No modeled module has a `remove` hook, so removal is
immediate.
-/
import Snabbdom.Dom

namespace Snabbdom

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

/-- Scala's `PatchedVNode`. -/
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

def sameVnode : PNode → VNode → Bool
  | .text _ _, .text _ => true
  | .elem s1 d1 _ _, .elem s2 d2 _ => d1.key == d2.key && d1.is == d2.is && s1 == s2
  | _, _ => false

/-- `Selector.parse`: the split of a selector such as `div#app.a.b` into the tag, the
`id` and the `class` it sets. Transcribed index for index, quirks included:
`div.a#b` gives tag `div.a` and id `b`. -/
structure Selector where
  tag : String
  id : Option String
  cls : Option String

def Selector.parse (sel : String) : Selector :=
  let cs := sel.toList
  let len := cs.length
  let slice (a b : Nat) := String.ofList ((cs.drop a).take (b - a))
  -- `sel.indexOf(".", hashIdx)`: JavaScript reads a negative start as 0
  let hashIdx := cs.findIdx? (· = '#')
  let dotFrom := hashIdx.getD 0
  let dotIdx := ((cs.drop dotFrom).findIdx? (· = '.')).map (· + dotFrom)
  let hash := match hashIdx with | some (i + 1) => i + 1 | _ => len
  let dot := match dotIdx with | some (i + 1) => i + 1 | _ => len
  { tag := if hashIdx.isSome || dotIdx.isSome then slice 0 (min hash dot) else sel
    id := if hash < dot then some (slice (hash + 1) dot) else none
    cls := match dotIdx with
      | some (_ + 1) => some (String.ofList ((cs.drop (dot + 1)).map fun c => if c = '.' then ' ' else c))
      | _ => none }

/-- `Selector.attr` -/
def Selector.attr (s : Selector) (k : String) : Option String :=
  if k = "id" then s.id else if k = "class" then s.cls else none

/-- The Scala code sets these with `elm.setAttribute`, outside any module. -/
def setSelectorAttrs (n : NodeId) (s : Selector) (d : Dom) : Dom :=
  let d := match s.id with | some i => d.setAttr n "id" i | none => d
  match s.cls with | some c => d.setAttr n "class" c | none => d

/-! ## The Attributes module (modules/Attributes.scala) -/

def xmlNS : String := "http://www.w3.org/XML/1998/namespace"
def xmlnsNS : String := "http://www.w3.org/2000/xmlns/"
def xlinkNS : String := "http://www.w3.org/1999/xlink"

/-- `namespaceOf` -/
def namespaceOf (k : String) : Option String :=
  if k.startsWith "xml:" then some xmlNS
  else if k.startsWith "xmlns:" then some xmlnsNS
  else if k.startsWith "xlink:" then some xlinkNS
  else none

/-- The prefix `namespaceOf` reads each of its namespaces from. -/
def nsPrefix (ns : String) : String :=
  if ns = xmlNS then "xml" else if ns = xmlnsNS then "xmlns" else "xlink"

/-- The qualified name of the attribute key `k` sets. -/
def attrName (k : String) : String := if (namespaceOf k).isSome then k else asciiLower k

/-- `set`. A namespaced key also removes the attribute with no namespace and
the whole key as local name, which is what HTML markup such as
`<div xml:lang="fr">` parses to and `toVNode` hydrates. -/
def setKey (d : Dom) (n : NodeId) (k v : String) : Dom :=
  match namespaceOf k with
  | none => d.setAttr n k v
  | some ns => (d.setAttrNS n ns k v).removeAttrNS n none k

/-- `remove`, which removes the hydrated attribute as `setKey` does. -/
def removeKey (d : Dom) (n : NodeId) (k : String) : Dom :=
  match namespaceOf k with
  | none => d.removeAttr n k
  | some ns => (d.removeAttrNS n (some ns) (splitQName k).2).removeAttrNS n none k

/-- `write` -/
def applyAttr (d : Dom) (n : NodeId) (k : String) : AttrVal → Dom
  | .bool true => setKey d n k ""
  | .bool false => removeKey d n k
  | .str s => setKey d n k s

/-- `drop`, on an HTML element, the only kind the model has. -/
def dropAttr (sel : String) (d : Dom) (n : NodeId) (k : String) : Dom :=
  match (Selector.parse sel).attr (asciiLower k) with
  | some v => d.setAttr n k v
  | none => removeKey d n k

def setAttrs (n : NodeId) (attrs : Attrs) (d : Dom) : Dom :=
  attrs.foldl (fun d kv => applyAttr d n kv.1 kv.2) d

def updateAttrs (sel : String) (n : NodeId) (old new : Attrs) (d : Dom) : Dom :=
  let d := old.foldl (fun d kv => if (new.lookup kv.1).isNone then dropAttr sel d n kv.1 else d) d
  new.foldl (fun d kv => if old.lookup kv.1 ≠ some kv.2 then applyAttr d n kv.1 kv.2 else d) d

/-- `cbs.create` -/
def moduleCreate (p : PNode) (d : Dom) : Dom :=
  match p with
  | .elem _ data _ n => if data.attrs ≠ [] then setAttrs n data.attrs d else d
  | _ => d

/-- `cbs.update` -/
def moduleUpdate (old : PNode) (v : VNode) (d : Dom) : Dom :=
  match old, v with
  | .elem _ a _ n, .elem sel b _ => if a.attrs ≠ b.attrs then updateAttrs sel n a.attrs b.attrs d else d
  | _, _ => d

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
    let s := Selector.parse sel
    let (n, d) := d.createElement s.tag
    let (pch, d) := createElms ch d
    let p := PNode.elem sel data pch n
    let d := setSelectorAttrs n s d
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

def removeAllVnodes (parentElm : NodeId) : List PNode → Dom → Dom
  | [], d => d
  | .elem _ _ _ n :: rest, d =>
    -- the remove callback removes the node from its *current* parent, which
    -- by now may differ from `parentElm`
    let d := match d.parentNode n with
      | some p => d.removeChild p n
      | none => d
    removeAllVnodes parentElm rest d
  | o :: rest, d => removeAllVnodes parentElm rest (d.removeChild parentElm o.node)

inductive Placement where
  /-- unkeyed match, never moved -/
  | anchored (child : PNode)
  /-- keyed match or newly created -/
  | movable (child : PNode)
  deriving Repr, Inhabited

def Placement.child : Placement → PNode
  | .anchored c | .movable c => c

/-- Scala's `KeyIndex` before any claim: the old children with key `k`, in
sibling order. Unlike `KeyIndex` it also holds the children before `start`, but
the fold has claimed all of those by the time it leaves the prefix (see
`matchedPrefix`), so `KeyIndex.claim` and `matchOne` pick the same child. -/
def keyedOld (oldCh : List PNode) (k : String) : List PNode :=
  oldCh.filter (·.key == some k)

/-- Scala's `nextReconciled`, written as a search over the siblings from the
cursor on. -/
def nextReconciled (d : Dom) (reconciled : List NodeId) : Option NodeId → Option NodeId
  | none => none
  | some o => (d.siblingsFrom o).find? (· ∈ reconciled)

/-- `.movable` is Scala's `oldIndex(k) < 0 || isKeyed(news(k))`. -/
def placeAroundAnchors (parentElm : NodeId) (reconciled : List NodeId) :
    List Placement → Option NodeId → Dom → Dom
  | [], _, d => d
  | .anchored c :: rest, _, d => placeAroundAnchors parentElm reconciled rest (d.nextSibling c.node) d
  | .movable c :: rest, cursor, d =>
    let reference := nextReconciled d reconciled cursor
    if reference = some c.node then
      placeAroundAnchors parentElm reconciled rest (d.nextSibling c.node) d
    else
      placeAroundAnchors parentElm reconciled rest reference (d.insertBefore parentElm c.node reference)

/-- After the prefix, an anchored placement is what sets Scala's
`anchoredAfterStart`. -/
def Placement.isAnchored : Placement → Bool
  | .anchored _ => true
  | .movable _ => false

/-- Scala's `oldIndex`: the position in `oldCh` of the old child a placement
reuses, `-1` for a created one. A reused child keeps its old node, and a created
one has a fresh node, so the node identifies the position. -/
def oldIndexOf (oldCh : List PNode) (pl : Placement) : Int :=
  match oldCh.findIdx? (·.node = pl.child.node) with
  | some i => i
  | none => -1

/-- Scala's `start`, recovered from `oldIndex`: how many leading children reused
the old child at their own position. It stops where Scala's prefix loop stops,
so the matching fold makes the same calls as the prefix loop and the general
loop together:
* inside Scala's prefix, `sameVnode(olds(j), news(j))` holds, and the fold
  claims `olds(j)`: an unkeyed child takes its position, and a keyed one takes
  the first unclaimed `sameVnode` old child with its key, which is `olds(j)`
  because every earlier old child is already claimed;
* where Scala's prefix stops, `sameVnode` fails against `olds(j)` (or there is
  none), so neither rule picks it and the count stops there too. -/
def matchedPrefix : List Int → Nat → Nat
  | [], _ => 0
  | i :: is, j => if i = j then matchedPrefix is (j + 1) + 1 else 0

/-- The binary search of Scala's `longestIncreasingRun`: where `seq ∘ tails`
increases on `[lo, hi)`, the least `m` there with `value ≤ seq (tails m)`, or
`hi`. -/
def lisSearch (seq : Nat → Int) (tails : Nat → Nat) (value : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if seq (tails mid) < value then lisSearch seq tails value (mid + 1) hi
    else lisSearch seq tails value lo mid
  else lo
termination_by hi - lo

/-- The `tails`, `previous` and `length` of Scala's `longestIncreasingRun`. -/
structure LisState where
  tails : Nat → Nat
  previous : Nat → Int
  length : Nat

/-- One iteration of `while (i < n)` in Scala's `longestIncreasingRun`. -/
def lisStep (seq : Nat → Int) (s : LisState) (i : Nat) : LisState :=
  if 0 ≤ seq i then
    let lo := lisSearch seq s.tails (seq i) 0 s.length
    { tails := fun m => if m = lo then i else s.tails m
      previous := fun j => if j = i then (if 0 < lo then (s.tails (lo - 1) : Int) else -1)
        else s.previous j
      length := if lo = s.length then s.length + 1 else s.length }
  else s

/-- The final `while (k >= 0)` of Scala's `longestIncreasingRun`. Each step
goes to a smaller index, so fuel equal to the length always reaches `-1`. -/
def lisWalk (previous : Nat → Int) : Nat → Int → List Nat
  | 0, _ => []
  | fuel + 1, k => if 0 ≤ k then k.toNat :: lisWalk previous fuel (previous k.toNat) else []

/-- Returns the indexes in the run, last first, where Scala returns the
`inRun` flags. -/
def longestIncreasingRun (seq : List Int) : List Nat :=
  let f : Nat → Int := fun i => seq.getD i (-1)
  let s := (List.range seq.length).foldl (lisStep f) ⟨fun _ => 0, fun _ => -1, 0⟩
  lisWalk s.previous seq.length (if 0 < s.length then (s.tails (s.length - 1) : Int) else -1)

/-- The `while (k <= end)` loop of Scala's `placeWithFewestMoves`. -/
def insertAllBefore (p : NodeId) (next : Option NodeId) : List NodeId → Dom → Dom
  | [], d => d
  | n :: ns, d => insertAllBefore p next ns (d.insertBefore p n next)

/-- The `while (end >= 0)` loop of Scala's `placeWithFewestMoves`, over the
children last first, each with whether it stays. Walking backward, the moving
children since the last staying one are buffered in sibling order; once the
block is complete, they go in first to last before `next`, the staying child
after them (or at the end), as in Scala. -/
def placeFewest (p : NodeId) : List (NodeId × Bool) → List NodeId → Option NodeId → Dom → Dom
  | [], blk, next, d => insertAllBefore p next blk d
  | (n, true) :: rest, blk, next, d => placeFewest p rest [] (some n) (insertAllBefore p next blk d)
  | (n, false) :: rest, blk, next, d => placeFewest p rest (n :: blk) next d

def placeWithFewestMoves (p : NodeId) (ns : List NodeId) (oldIndex : List Int) (d : Dom) : Dom :=
  let run := longestIncreasingRun oldIndex
  let stays := (List.range ns.length).map (fun i => decide (i ∈ run))
  placeFewest p (ns.zip stays).reverse [] none d

/-- The rest of `updateChildren` after the matching fold. -/
def finishChildren (parentElm : NodeId) (oldCh : List PNode) (pls : List Placement)
    (d : Dom) : List PNode × Dom :=
  let oldIndex := pls.map (oldIndexOf oldCh)
  let start := matchedPrefix oldIndex 0
  let children := pls.map (·.child)
  if start = oldCh.length then
    (children, appendAll parentElm (children.drop start) d)
  else
    let reconciled := pls.map (·.child.node)
    let d := if (pls.drop start).any (·.isAnchored) then
        placeAroundAnchors parentElm reconciled pls (oldCh.head?.map (·.node)) d
      else placeWithFewestMoves parentElm reconciled oldIndex d
    let d := removeAllVnodes parentElm (oldCh.filter (fun o => o.node ∉ reconciled)) d
    (children, d)

/-- `patchVnode`'s `case (Nil, _ :: _)`. -/
def createAndInsert (elm : NodeId) : List VNode → Dom → List PNode × Dom
  | [], d => ([], d)
  | v :: vs, d =>
    let (p, d) := createElm v d
    let d := d.insertBefore elm p.node none
    let (ps, d) := createAndInsert elm vs d
    (p :: ps, d)

/-- One iteration of the prefix loop or of `while (j < newLen)` in
`updateChildren`: find the old child that `v` reuses (`KeyIndex.claim` for a
keyed `v`), or create a fresh one. `pv o d` patches `o` into `v`. `pos` is the
index of `v`; `byKey` holds the old keyed children not claimed yet. -/
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
    | _, _ => (old, d.fail) -- Scala throws "trying to patch incompatible nodes"

def matchChildren (oldCh : List PNode) (byKey : String → List PNode) (pos : Nat) :
    List VNode → Dom → List Placement × Dom
  | [], d => ([], d)
  | v :: vs, d =>
    let (pl, byKey', d) := matchOne oldCh byKey pos v (fun o d => patchVnode o v d) d
    let (pls, d) := matchChildren oldCh byKey' (pos + 1) vs d
    (pl :: pls, d)
end

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
