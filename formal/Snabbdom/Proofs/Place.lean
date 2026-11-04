/-
`place` on the DOM heap does what `placeL` does to the parent's child list,
and touches nothing else except the parent pointers of the placed nodes.
-/
import Snabbdom.Proofs.PlaceList
import Snabbdom.Proofs.Create

namespace Snabbdom

def Placement.toPair : Placement → Bool × NodeId
  | .anchored c => (true, c.node)
  | .movable c => (false, c.node)

theorem Placement.toPair_snd (pl : Placement) : pl.toPair.2 = pl.child.node := by
  cases pl <;> rfl

theorem toPairs_snd (P : List Placement) : (P.map Placement.toPair).map (·.2) = P.map (·.child.node) := by
  simp [Function.comp_def, Placement.toPair_snd]

theorem after_not_mem (c : NodeId) (L : List NodeId) (h : c ∉ L) : after c L = none := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [after, Ne.symm h.1, ite_false]; exact ih h.2

theorem after_mem (c x : NodeId) (L : List NodeId) (h : after c L = some x) : x ∈ L := by
  induction L with
  | nil => simp [after] at h
  | cons y ys ih =>
    simp only [after] at h
    split at h
    · cases ys with
      | nil => simp at h
      | cons z zs => simp at h; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem refOf_mem (R L : List NodeId) (cur : Option NodeId) (x : NodeId)
    (h : refOf R L cur = some x) : x ∈ L := by
  cases cur with
  | none => simp [refOf] at h
  | some o =>
    simp only [refOf] at h
    exact (List.dropWhile_sublist _).subset (List.mem_of_find?_eq_some h)

namespace Dom

theorem parent_of_mem {d : Dom} (h : HeapWF d) {p : NodeId} {px : DomNode} (hp : d.nodes p = some px)
    {c : NodeId} (hc : c ∈ px.children) : d.parentNode c = some p := by
  obtain ⟨cx, hcx, hcp⟩ := h.child_parent p px c hp hc
  simp [parentNode_eq, hcx, hcp]

theorem nextSibling_eq {d : Dom} (h : HeapWF d) {p : NodeId} {px : DomNode} (hp : d.nodes p = some px)
    {c : NodeId} {cx : DomNode} (hc : d.nodes c = some cx)
    (hpar : cx.parent = none ∨ cx.parent = some p) : d.nextSibling c = after c px.children := by
  rcases hpar with hpar | hpar
  · have hnot : c ∉ px.children := by
      intro hm; obtain ⟨y, hy, hyp⟩ := h.child_parent p px c hp hm
      rw [hc] at hy; cases hy; rw [hpar] at hyp; cases hyp
    rw [after_not_mem c _ hnot]
    simp [nextSibling, parentNode_eq, hc, hpar]
  · simp [nextSibling, parentNode_eq, hc, hpar, hp]

theorem nextReconciledNode_eq {d : Dom} (h : HeapWF d) {p : NodeId} {px : DomNode}
    (hp : d.nodes p = some px) (R : List NodeId) (cur : Option NodeId)
    (hcur : cur = none ∨ ∃ o, cur = some o ∧ o ∈ px.children) :
    nextReconciledNode d R cur = refOf R px.children cur := by
  rcases hcur with rfl | ⟨o, rfl, ho⟩
  · rfl
  · simp only [nextReconciledNode, refOf, siblingsFrom, parent_of_mem h hp ho, get_eq, hp]

end Dom

theorem place_spec (elm : NodeId) (R : List NodeId) :
    ∀ (P : List Placement) (cur : Option NodeId) (d : Dom) (ex : DomNode),
    HeapWF d → d.nodes elm = some ex →
    (cur = none ∨ ∃ o, cur = some o ∧ o ∈ ex.children) →
    (P.map (·.child.node)).Nodup →
    (∀ pl ∈ P, pl.child.node ≠ elm ∧ ∃ x, d.nodes pl.child.node = some x ∧
      (x.parent = none ∨ x.parent = some elm)) →
    HeapWF (place elm R P cur d) ∧ (place elm R P cur d).ok = d.ok ∧
    (place elm R P cur d).next = d.next ∧
    (place elm R P cur d).nodes elm =
      some { ex with children := placeL R (P.map Placement.toPair) cur ex.children } ∧
    (∀ m, m ≠ elm → SameContent d (place elm R P cur d) m) ∧
    (∀ m, m ≠ elm → m ∉ P.map (·.child.node) → (place elm R P cur d).nodes m = d.nodes m)
  | [], cur, d, ex, hw, he, _, _, _ => by
    simp only [place, List.map_nil, placeL]
    exact ⟨hw, trivial, trivial, by rw [he], fun m _ => SameContent.of_eq rfl, fun _ _ _ => trivial⟩
  | .anchored c :: rest, cur, d, ex, hw, he, _, hnd, hP => by
    obtain ⟨_, cx, hcx, hpar⟩ := hP _ List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Placement.child] at hcx
    have hns : d.nextSibling c.node = after c.node ex.children := Dom.nextSibling_eq hw he hcx hpar
    have hcur' : d.nextSibling c.node = none ∨ ∃ o, d.nextSibling c.node = some o ∧ o ∈ ex.children := by
      rw [hns]; cases h : after c.node ex.children with
      | none => exact Or.inl rfl
      | some o => exact Or.inr ⟨o, rfl, after_mem _ _ _ h⟩
    obtain ⟨w, ok, nx, ne, sc, fr⟩ := place_spec elm R rest _ d ex hw he hcur' hnd.2
      (fun pl hpl => hP pl (List.mem_cons_of_mem _ hpl))
    simp only [place, List.map_cons, Placement.toPair, placeL]
    rw [← hns]
    exact ⟨w, ok, nx, ne, sc, fun m hm hm' => fr m hm (fun h => hm' (List.mem_cons_of_mem _ h))⟩
  | .movable c :: rest, cur, d, ex, hw, he, hcur, hnd, hP => by
    obtain ⟨hce, cx, hcx, hpar⟩ := hP _ List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Placement.child] at hce hcx
    have hrest : ∀ pl ∈ rest, pl.child.node ≠ elm ∧ ∃ x, d.nodes pl.child.node = some x ∧
        (x.parent = none ∨ x.parent = some elm) := fun pl hpl => hP pl (List.mem_cons_of_mem _ hpl)
    have hns : d.nextSibling c.node = after c.node ex.children := Dom.nextSibling_eq hw he hcx hpar
    have hnr := Dom.nextReconciledNode_eq hw he R cur hcur
    simp only [place, List.map_cons, Placement.toPair, placeL]
    rw [hnr]
    split
    · rename_i heq
      have hcur' : d.nextSibling c.node = none ∨ ∃ o, d.nextSibling c.node = some o ∧ o ∈ ex.children := by
        rw [hns]; cases h : after c.node ex.children with
        | none => exact Or.inl rfl
        | some o => exact Or.inr ⟨o, rfl, after_mem _ _ _ h⟩
      obtain ⟨w, ok, nx, ne, sc, fr⟩ := place_spec elm R rest _ d ex hw he hcur' hnd.2 hrest
      rw [← hns]
      exact ⟨w, ok, nx, ne, sc, fun m hm hm' => fr m hm (fun h => hm' (List.mem_cons_of_mem _ h))⟩
    · rename_i hne
      let ref := refOf R ex.children cur
      have hi : Dom.InsertOk (d.log (.insertBefore elm c.node ref)) elm c.node ref ex cx :=
        ⟨he, hcx, hce, hpar, fun r hr => ⟨refOf_mem R _ cur r hr, fun e => hne (by subst e; exact hr)⟩⟩
      have hwl := Dom.log_wf (.insertBefore elm c.node ref) hw
      have hN := Dom.preInsert_nodes hwl hi
      let d1 := d.insertBefore elm c.node ref
      have hd1 : d1 = (d.log (.insertBefore elm c.node ref)).preInsert elm c.node ref := rfl
      have w1 : HeapWF d1 := hd1 ▸ Dom.preInsert_wf hwl hi
      have he1 : d1.nodes elm = some { ex with children := insertAt c.node ref (ex.children.erase c.node) } := by
        rw [hd1, hN]; simp
      have hcur1 : ref = none ∨ ∃ o, ref = some o ∧ o ∈ (insertAt c.node ref (ex.children.erase c.node)) := by
        cases h : ref with
        | none => exact Or.inl rfl
        | some r =>
          refine Or.inr ⟨r, rfl, ?_⟩
          have hr := hi.ref_ok r h
          rw [mem_insertAt]; exact Or.inr ((List.mem_erase_of_ne hr.2).2 hr.1)
      have hrest1 : ∀ pl ∈ rest, pl.child.node ≠ elm ∧ ∃ x, d1.nodes pl.child.node = some x ∧
          (x.parent = none ∨ x.parent = some elm) := by
        intro pl hpl
        obtain ⟨h1, x, hx, hxp⟩ := hrest pl hpl
        have : pl.child.node ≠ c.node := fun e => hnd.1 (e ▸ List.mem_map_of_mem hpl)
        exact ⟨h1, x, by rw [hd1, hN]; simp [h1, this, hx], hxp⟩
      obtain ⟨w, ok, nx, ne, sc, fr⟩ := place_spec elm R rest ref d1 _ w1 he1 hcur1 hnd.2 hrest1
      refine ⟨w, ?_, ?_, ne, ?_, ?_⟩
      · rw [ok, hd1, Dom.preInsert_ok hi]; rfl
      · rw [nx, hd1]; simp
      · intro m hm
        refine SameContent.trans ?_ (sc m hm)
        unfold SameContent
        rw [hd1, hN, ite_eq_right hm]
        split
        · rename_i h; subst h; simp [hcx, DomNode.content]
        · rfl
      · intro m hm hm'
        simp only [List.mem_cons, not_or] at hm'
        have hm1 : m ≠ c.node := hm'.1
        rw [fr m hm hm'.2, hd1, hN, ite_eq_right hm, ite_eq_right hm1]; rfl

end Snabbdom
