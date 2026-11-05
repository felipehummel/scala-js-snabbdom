/-
The library inputs that `AttrsWF` excludes, run through the model: patching
leaves a different element than rendering the new vnode from scratch. The
conformance suite replays the same two cases against the Scala code.
-/
import Snabbdom.Model

namespace Snabbdom

private def patchedAttr (old new : VNode) (k : String) : Option String :=
  let (pv, d) := createElm old Dom.empty
  let (nv, d) := patch pv new d
  (d.get nv.node).bind (·.attrs k)

private def freshAttr (v : VNode) (k : String) : Option String :=
  let (nv, d) := createElm v Dom.empty
  (d.get nv.node).bind (·.attrs k)

-- `div#a` with an `id` attribute, patched to `div#a` without one: the update
-- removes `id`, so the selector's `id="a"` is gone too.
#guard patchedAttr (.elem "div#a" { attrs := [("id", .str "z")] } []) (.elem "div#a" {} []) "id" = none
#guard freshAttr (.elem "div#a" {} []) "id" = some "a"

-- `TITLE` patched to `title`: the update sets `title`, then removes `TITLE`,
-- which the DOM reads as `title`.
#guard patchedAttr (.elem "div" { attrs := [("TITLE", .str "x")] } [])
  (.elem "div" { attrs := [("title", .str "y")] } []) "title" = none
#guard freshAttr (.elem "div" { attrs := [("title", .str "y")] } []) "title" = some "y"

end Snabbdom
