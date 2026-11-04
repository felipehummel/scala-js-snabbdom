/-
Conformance check between the Lean model and the Scala implementation.

Input: one JSON object per line, written by the Scala `ConformanceSuite`
(snabbdom/src/conformance). Each case has the old vnode, the new vnode, the
`DomApi` calls the Scala `patch(old, new)` made, and the resulting DOM.

For each case this program renders `old` with the model, runs the model's
`patch old new`, and checks that it makes exactly the same `DomApi` calls and
leaves exactly the same DOM.
-/
import Snabbdom
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

partial def attrKeys : VNode → List String
  | .elem _ d ch => d.attrs.map (·.1) ++ ch.flatMap attrKeys
  | _ => []

/-- Same format as `ConformanceSuite.serialize` on the Scala side. -/
partial def serialize (d : Dom) (keys : List String) (n : NodeId) : String :=
  match d.get n with
  | none => "?"
  | some x =>
    match x.kind with
    | .text s => "\"" ++ s ++ "\""
    | .comment s => "<!--" ++ s ++ "-->"
    | .elem sel =>
      let attrs := keys.filterMap fun k => (x.attrs k).map fun v => s!" {k}=\"{v}\""
      "<" ++ sel ++ String.join attrs ++ ">" ++
        String.join (x.children.map (serialize d keys)) ++ "</" ++ sel ++ ">"

structure Outcome where
  ok : Bool
  message : String

def runCase (line : String) : Except String Outcome := do
  let j ← Json.parse line
  let old ← parseVNode (← j.getObjVal? "old")
  let new ← parseVNode (← j.getObjVal? "new")
  let scalaTrace ← (← (← j.getObjVal? "trace").getArr?).toList.mapM (·.getStr?)
  let scalaDom ← j.getObjValAs? String "dom"
  -- node 0 is the host element; the old tree is rendered into it
  let (host, d) := Dom.empty.alloc (.elem "host")
  let (pv, d) := createElm old d
  let d := d.appendChild host pv.node
  let d := { d with trace := #[] }
  let (_, d) := patch pv new d
  let leanTrace := d.trace.toList.map Op.render
  let keys := ((attrKeys old ++ attrKeys new).mergeSort (· ≤ ·)).eraseDups
  let leanDom := String.join (((d.get host).map (·.children)).getD [] |>.map (serialize d keys))
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
