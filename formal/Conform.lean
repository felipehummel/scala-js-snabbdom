/-
Input: one JSON object per line from the Scala `ConformanceSuite`, with fields
`old` and `new` (vnodes), `detached` (whether `old` was patched outside any
parent), `sibling` (whether the host holds an `x-sibling` element after `old`),
`trace` (Scala's `DomApi` calls, rendered as by `Op.render`) and `dom`
(rendered as by `serialize`). Node ids in `trace` must be allocated as the
model allocates them: the host is 0, then `old` in pre-order, then the sibling.
-/
import Snabbdom.Model
import Lean.Data.Json

open Lean Snabbdom

def parseAttr (j : Json) : Except String (String × AttrVal) := do
  let arr ← j.getArr?
  let k ← (arr[0]?.getD Json.null).getStr?
  let v := arr[1]?.getD Json.null
  match v.getStr? with
  | .ok s => pure (k, .str s)
  | .error _ => pure (k, .bool (← v.getBool?))

partial def parseVNode (j : Json) : Except String VNode :=
  match j.getObjValAs? String "x", j.getObjValAs? String "c" with
  | .ok s, _ => pure (.text s)
  | _, .ok s => pure (.comment s)
  | _, _ => do
    let sel ← j.getObjValAs? String "sel"
    let key := (j.getObjValAs? String "key").toOption
    let attrs ← (← (← j.getObjVal? "attrs").getArr?).toList.mapM parseAttr
    let ch ← (← (← j.getObjVal? "ch").getArr?).toList.mapM parseVNode
    pure (.elem sel { key, attrs } ch)

def Op.render : Op → String
  | .createElement n t => s!"ce {n} {t}"
  | .createText n s => s!"ct {n} {s}"
  | .createComment n s => s!"cc {n} {s}"
  | .insertBefore p n r => s!"ib {p} {n} {r.elim "-" toString}"
  | .appendChild p n => s!"ac {p} {n}"
  | .removeChild p n => s!"rc {p} {n}"
  | .setText n s => s!"st {n} {s}"

/-- ` name="value"`, with `{namespace}` before the name when it has one. -/
def Attr.render (a : Attr) : String :=
  " " ++ a.ns.elim "" (fun ns => "{" ++ ns ++ "}") ++ a.qname ++ "=\"" ++ a.value ++ "\""

/-- Same format as `ConformanceSuite.serialize` on the Scala side: attributes
sorted by qualified name, then namespace. -/
partial def serialize (d : Dom) (n : NodeId) : String :=
  match d.get n with
  | none => "?"
  | some x =>
    match x.kind with
    | .text s => "\"" ++ s ++ "\""
    | .comment s => "<!--" ++ s ++ "-->"
    | .elem tag =>
      let sorted := x.attrs.mergeSort fun a b =>
        a.qname < b.qname || (a.qname == b.qname && a.ns.getD "" ≤ b.ns.getD "")
      "<" ++ tag ++ String.join (sorted.map Attr.render) ++ ">" ++
        String.join (x.children.map (serialize d)) ++ "</" ++ tag ++ ">"

structure Outcome where
  ok : Bool
  message : String

def runCase (line : String) : Except String Outcome := do
  let j ← Json.parse line
  let old ← parseVNode (← j.getObjVal? "old")
  let new ← parseVNode (← j.getObjVal? "new")
  let scalaTrace ← (← (← j.getObjVal? "trace").getArr?).toList.mapM (·.getStr?)
  let detached ← j.getObjValAs? Bool "detached"
  let sibling ← j.getObjValAs? Bool "sibling"
  let scalaDom ← j.getObjValAs? String "dom"
  let (host, d) := Dom.empty.alloc (.elem "host")
  let (pv, d) := createElm old d
  let d := if detached then d else d.appendChild host pv.node
  let d := if sibling then (let (s, d) := d.alloc (.elem "x-sibling"); d.appendChild host s) else d
  let d := { d with trace := #[] }
  let (nv, d) := patch pv new d
  let leanTrace := d.trace.toList.map Op.render
  let hostDom := String.join (((d.get host).map (·.children)).getD [] |>.map (serialize d))
  let leanDom := hostDom ++ "|" ++ serialize d nv.node
  if !d.ok then
    return ⟨false, "model reached a DOM error"⟩
  if leanTrace ≠ scalaTrace then
    return ⟨false, s!"trace differs\n  scala: {scalaTrace}\n  lean:  {leanTrace}"⟩
  if leanDom ≠ scalaDom then
    return ⟨false, s!"DOM differs\n  scala: {scalaDom}\n  lean:  {leanDom}"⟩
  return ⟨true, ""⟩

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: conform <cases.jsonl>"; return 2
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let mut failures := 0
  let mut ops := 0
  for line in lines do
    match runCase line with
    | .error e =>
      failures := failures + 1
      IO.eprintln s!"cannot parse case: {e}\n{line}"
    | .ok o =>
      if !o.ok then
        failures := failures + 1
        if failures ≤ 5 then IO.eprintln s!"MISMATCH: {o.message}\n  case: {line}\n"
  for line in lines do
    if let .ok j := Json.parse line then
      if let .ok t := j.getObjVal? "trace" then
        if let .ok a := t.getArr? then ops := ops + a.size
  IO.println s!"{lines.size} cases, {ops} DOM operations compared, {failures} mismatches"
  return if failures = 0 && lines.size > 0 then 0 else 1
