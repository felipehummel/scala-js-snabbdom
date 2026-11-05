/-
Fails the build if a main theorem picks up `sorry` (`sorryAx`) or any axiom
beyond Lean's standard three, which `lake build` would otherwise accept with
only a warning.
-/
import Snabbdom.Proofs.Main

/-- info: 'Snabbdom.diff_eq_recreate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Snabbdom.diff_eq_recreate

/-- info: 'Snabbdom.patch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Snabbdom.patch_correct

/-- info: 'Snabbdom.createElm_shows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Snabbdom.createElm_shows
