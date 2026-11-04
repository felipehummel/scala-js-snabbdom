/-
Pieces of child reconciliation: node identity in a child list, removal,
create-and-append, and what `placeL` keeps.
-/
import Snabbdom.Proofs.Place

namespace Snabbdom

/-! ### Node identity among siblings -/

theorem PNode.mem_ids_of_mem {L : List PNode} {o : PNode} {i : NodeId} (ho : o ∈ L) (hi : i ∈ o.ids) :
    i ∈ PNode.idsList L := PNode.mem_idsList.2 ⟨o, ho, hi⟩

/-- Two siblings sharing a node id are the same sibling. -/
theorem PNode.ids_inj : ∀ (L : List PNode) {o o' : PNode} {i : NodeId}, (PNode.idsList L).Nodup →
    o ∈ L → o' ∈ L → i ∈ o.ids → i ∈ o'.ids → o = o'
  | [], _, _, _, _, ho, _, _, _ => by cases ho
  | a :: L, o, o', i, hn, ho, ho', hi, hi' => by
    rw [PNode.idsList_cons, List.nodup_append] at hn
    rcases List.mem_cons.1 ho with h1 | h1 <;> rcases List.mem_cons.1 ho' with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd rfl (hn.2.2 i hi i (PNode.mem_ids_of_mem h2 hi'))
    · subst h2; exact absurd rfl (hn.2.2 i hi' i (PNode.mem_ids_of_mem h1 hi))
    · exact PNode.ids_inj L hn.2.1 h1 h2 hi hi'

theorem PNode.node_inj {L : List PNode} {o o' : PNode} (hn : (PNode.idsList L).Nodup)
    (ho : o ∈ L) (ho' : o' ∈ L) (h : o.node = o'.node) : o = o' :=
  PNode.ids_inj L hn ho ho' (PNode.node_mem_ids o) (h ▸ PNode.node_mem_ids o')

theorem PNode.roots_nodup : ∀ (L : List PNode), (PNode.idsList L).Nodup → (L.map PNode.node).Nodup
  | [], _ => by simp
  | c :: cs, hn => by
    have hn' := hn
    rw [PNode.idsList_cons, List.nodup_append] at hn'
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, PNode.roots_nodup cs hn'.2.1⟩
    obtain ⟨c', hc', he⟩ := List.mem_map.1 hm
    exact hn'.2.2 c.node (PNode.node_mem_ids c) c.node
      (PNode.mem_idsList.2 ⟨c', hc', he ▸ PNode.node_mem_ids c'⟩) rfl

theorem idx_inj : ∀ (L : List NodeId) (i j : Nat) (x : NodeId), L.Nodup → L[i]? = some x → L[j]? = some x → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | a :: L, 0, 0, _, _, _, _ => rfl
  | a :: L, 0, j + 1, x, hn, hi, hj => by
    simp at hi hj; subst hi
    exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.1 hn).1
  | a :: L, i + 1, 0, x, hn, hi, hj => by
    simp at hi hj; subst hj
    exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.1 hn).1
  | a :: L, i + 1, j + 1, x, hn, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    rw [idx_inj L i j x (List.nodup_cons.1 hn).2 hi hj]

theorem sameVnode_key (o : PNode) (v : VNode) (h : sameVnode o v = true) : o.key = v.key := by
  cases o <;> cases v <;> simp_all [sameVnode, PNode.key, VNode.key]

theorem sameVnode_sel {osel : String} {od : Data} {och : List PNode} {n : NodeId} {sel : String}
    {data : Data} {ch : List VNode} (h : sameVnode (.elem osel od och n) (.elem sel data ch) = true) :
    osel = sel := by
  simp only [sameVnode, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem span_loop_cons {α} (p : α → Bool) : ∀ (l acc s r : List α) (o : α),
    List.span.loop p l acc = (s, o :: r) → acc.reverse ++ l = s ++ o :: r ∧ p o = false
  | [], acc, s, r, o, h => by simp [List.span.loop] at h
  | a :: as, acc, s, r, o, h => by
    simp only [List.span.loop] at h
    cases hp : p a
    · rw [hp] at h; simp only [Prod.mk.injEq, List.cons.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; exact ⟨rfl, hp⟩
    · rw [hp] at h
      obtain ⟨e, hpo⟩ := span_loop_cons p as (a :: acc) s r o h
      refine ⟨?_, hpo⟩
      rw [← e]; simp

theorem span_cons {α} (p : α → Bool) (l s r : List α) (o : α) (h : l.span p = (s, o :: r)) :
    l = s ++ o :: r ∧ p o = false := by
  have := span_loop_cons p l [] s r o h
  simpa using this

/-! ### What `placeL` keeps and adds -/

theorem placeL_keep (R : List NodeId) : ∀ (P : List (Bool × NodeId)) (cur : Option NodeId)
    (L : List NodeId) (x : NodeId), x ∈ L → x ∉ P.map (·.2) → x ∈ placeL R P cur L
  | [], _, _, _, h, _ => h
  | (true, c) :: rest, _, L, x, h, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    exact placeL_keep R rest _ L x h hn.2
  | (false, c) :: rest, cur, L, x, h, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [placeL]
    split
    · exact placeL_keep R rest _ L x h hn.2
    · apply placeL_keep R rest _ _ x _ hn.2
      rw [mem_insertAt]; exact Or.inr ((List.mem_erase_of_ne hn.1).2 h)

theorem placeL_sub (R : List NodeId) : ∀ (P : List (Bool × NodeId)) (cur : Option NodeId)
    (L : List NodeId) (x : NodeId), x ∈ placeL R P cur L → x ∈ L ∨ x ∈ P.map (·.2)
  | [], _, _, _, h => Or.inl h
  | (true, c) :: rest, _, L, x, h => by
    rcases placeL_sub R rest _ L x h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  | (false, c) :: rest, cur, L, x, h => by
    simp only [placeL] at h
    split at h
    · rcases placeL_sub R rest _ L x h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases placeL_sub R rest _ _ x h with h | h
      · rw [mem_insertAt] at h
        rcases h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl (List.mem_of_mem_erase h)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ### removeAllVnodes -/

theorem removeAll_cons (elm : NodeId) (o : PNode) (rest : List PNode) (d : Dom)
    (hp : d.parentNode o.node = some elm) :
    removeAllVnodes elm (o :: rest) d = removeAllVnodes elm rest (d.removeChild elm o.node) := by
  cases o with
  | elem sel data ch n => simp only [PNode.node] at hp; simp only [removeAllVnodes, hp, PNode.node]
  | text s n => rfl
  | comment s n => rfl

theorem filter_erase (L : List NodeId) (hL : L.Nodup) (a : NodeId) (S : List NodeId) :
    (L.erase a).filter (fun x => decide (x ∉ S)) = L.filter (fun x => decide (x ∉ a :: S)) := by
  rw [hL.erase_eq_filter, List.filter_filter]
  congr 1; funext x
  by_cases h : x = a <;> simp [h]

theorem removeAll_spec (elm : NodeId) : ∀ (os : List PNode) (d : Dom) (ex : DomNode),
    HeapWF d → d.nodes elm = some ex →
    (os.map PNode.node).Nodup →
    (∀ o ∈ os, o.node ∈ ex.children ∧ o.node ≠ elm) →
    HeapWF (removeAllVnodes elm os d) ∧ (removeAllVnodes elm os d).ok = d.ok ∧
    (removeAllVnodes elm os d).next = d.next ∧
    (removeAllVnodes elm os d).nodes elm =
      some { ex with children := ex.children.filter (fun x => decide (x ∉ os.map PNode.node)) } ∧
    (∀ m, m ≠ elm → SameContent d (removeAllVnodes elm os d) m) ∧
    (∀ m, m ≠ elm → m ∉ os.map PNode.node → (removeAllVnodes elm os d).nodes m = d.nodes m)
  | [], d, ex, hw, he, _, _ => by
    refine ⟨hw, rfl, rfl, ?_, fun m _ => SameContent.of_eq rfl, fun _ _ _ => rfl⟩
    simp only [removeAllVnodes, he]
    cases ex; simp only [List.map_nil, List.not_mem_nil, not_false_eq_true, decide_true,
      Option.some.injEq, DomNode.mk.injEq, true_and, and_true]
    exact (List.filter_eq_self.2 (by simp)).symm
  | o :: rest, d, ex, hw, he, hnd, hos => by
    obtain ⟨hm, hne⟩ := hos o List.mem_cons_self
    obtain ⟨cx, hcx, hcp⟩ := hw.child_parent elm ex o.node he hm
    rw [removeAll_cons elm o rest d (Dom.parent_of_mem hw he hm)]
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hN := Dom.removeChild_nodes he hcx hm hne
    have w1 := Dom.removeChild_wf hw he hcx hm hne
    let d1 := d.removeChild elm o.node
    have he1 : d1.nodes elm = some { ex with children := ex.children.erase o.node } := by
      show (d.removeChild elm o.node).nodes elm = _
      rw [hN]; simp
    have hrest : ∀ o' ∈ rest, o'.node ∈ { ex with children := ex.children.erase o.node }.children ∧
        o'.node ≠ elm := by
      intro o' ho'
      obtain ⟨hm', hne'⟩ := hos o' (List.mem_cons_of_mem _ ho')
      have : o'.node ≠ o.node := fun e => hnd.1 (e ▸ List.mem_map_of_mem ho')
      exact ⟨(List.mem_erase_of_ne this).2 hm', hne'⟩
    obtain ⟨w, ok, nx, ne, sc, fr⟩ := removeAll_spec elm rest d1 _ w1 he1 hnd.2 hrest
    refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ok]; exact Dom.removeChild_ok he hm
    · rw [nx]; exact Dom.removeChild_next _ _
    · rw [ne, filter_erase _ (hw.nodup elm ex he) o.node, List.map_cons]
    · intro m hm'
      refine SameContent.trans ?_ (sc m hm')
      unfold SameContent
      show ((d.removeChild elm o.node).nodes m).map _ = _
      rw [hN, ite_eq_right hm']
      split
      · rename_i h; subst h; simp [hcx, DomNode.content]
      · rfl
    · intro m hm1 hm2
      simp only [List.map_cons, List.mem_cons, not_or] at hm2
      rw [fr m hm1 hm2.2]
      show (d.removeChild elm o.node).nodes m = _
      rw [hN, ite_eq_right hm1, ite_eq_right hm2.1]

/-! ### createAndInsert -/

theorem createAndInsert_spec (elm : NodeId) : ∀ (vs : List VNode) (d : Dom) (ex : DomNode),
    HeapWF d → d.nodes elm = some ex → elm < d.next → VNode.WFs vs →
    HeapWF (createAndInsert elm vs d).2 ∧ (createAndInsert elm vs d).2.ok = d.ok ∧
    d.next ≤ (createAndInsert elm vs d).2.next ∧
    (createAndInsert elm vs d).2.nodes elm =
      some { ex with children := ex.children ++ (createAndInsert elm vs d).1.map PNode.node } ∧
    (∀ i, i < d.next → i ≠ elm → (createAndInsert elm vs d).2.nodes i = d.nodes i) ∧
    ReprList (createAndInsert elm vs d).2 (createAndInsert elm vs d).1 ∧
    (PNode.idsList (createAndInsert elm vs d).1).Nodup ∧
    (∀ i ∈ PNode.idsList (createAndInsert elm vs d).1, d.next ≤ i ∧ i < (createAndInsert elm vs d).2.next) ∧
    PNode.toVNodes (createAndInsert elm vs d).1 = vs
  | [], d, ex, hw, he, _, _ => by
    simp only [createAndInsert, List.map_nil, List.append_nil, he]
    refine ⟨hw, ?_, Nat.le_refl _, ?_, fun _ _ _ => ?_, trivial, by simp [PNode.idsList],
      by simp [PNode.idsList], ?_⟩ <;> first | trivial | rfl
  | v :: vs, d, ex, hw, he, hlt, hv => by
    obtain ⟨c1, tv1⟩ := createElm_spec v d hw hv.1
    generalize hr1 : createElm v d = r1 at c1 tv1
    obtain ⟨p, d1⟩ := r1
    simp only at c1 tv1
    obtain ⟨px, hpx, hpp⟩ := c1.detached
    have hpr := c1.ids_range p.node (PNode.node_mem_ids p)
    have hpne : p.node ≠ elm := by omega
    have he1 : d1.nodes elm = some ex := by rw [c1.frame elm hlt]; exact he
    have hi : Dom.InsertOk (d1.log (.insertBefore elm p.node none)) elm p.node none ex px :=
      ⟨he1, hpx, hpne, Or.inl hpp, fun r h => by cases h⟩
    have hwl := Dom.log_wf (.insertBefore elm p.node none) c1.wf
    have hN := Dom.preInsert_nodes hwl hi
    have hnot := hi.not_mem hwl hpp
    let d2 := d1.insertBefore elm p.node none
    have hd2 : d2 = (d1.log (.insertBefore elm p.node none)).preInsert elm p.node none := rfl
    have w2 : HeapWF d2 := hd2 ▸ Dom.preInsert_wf hwl hi
    have he2 : d2.nodes elm = some { ex with children := ex.children ++ [p.node] } := by
      rw [hd2, hN]; simp [insertAt_none, List.erase_of_not_mem hnot]
    have nx2 : d2.next = d1.next := by rw [hd2]; simp
    obtain ⟨w, ok, le, ne, fr, rp, nd, rg, tv⟩ :=
      createAndInsert_spec elm vs d2 _ w2 he2 (by rw [nx2]; have := c1.le; omega) hv.2
    generalize hr2 : createAndInsert elm vs d2 = r2 at w ok le ne fr rp nd rg tv
    obtain ⟨ps, d3⟩ := r2
    simp only at w ok le ne fr rp nd rg tv
    have hd : createAndInsert elm (v :: vs) d = (p :: ps, d3) := by
      simp only [createAndInsert, hr1]; rw [show d1.insertBefore elm p.node none = d2 from rfl, hr2]
    rw [hd]; dsimp only
    have le1 := c1.le
    -- d2 agrees with d1 below d1.next except at elm and p.node, whose contents are unchanged
    have sc12 : ∀ i, i ≠ elm → SameContent d1 d2 i := by
      intro i hie
      unfold SameContent; rw [hd2, hN, ite_eq_right hie]
      split
      · rename_i h; subst h; simp [hpx, DomNode.content]
      · rfl
    refine ⟨w, by rw [ok, hd2, Dom.preInsert_ok hi]; exact c1.ok, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ne]; simp
    · intro i hi1 hie
      rw [fr i (by omega) hie, hd2, hN, ite_eq_right hie, ite_eq_right (by omega)]
      exact c1.frame i hi1
    · refine ⟨Repr.frame p c1.repr (fun i hi' => ?_), rp⟩
      have := c1.ids_range i hi'
      have hie : i ≠ elm := by omega
      exact SameContent.trans (sc12 i hie) (SameContent.of_eq (fr i (by omega) hie))
    · rw [PNode.idsList_cons, List.nodup_append]
      refine ⟨c1.ids_nodup, nd, fun a ha b hb e => ?_⟩
      subst e
      have := (c1.ids_range a ha).2; have := (rg a hb).1; omega
    · intro i hi'
      rw [PNode.idsList_cons, List.mem_append] at hi'
      rcases hi' with hi' | hi'
      · have := c1.ids_range i hi'; omega
      · have := rg i hi'; omega
    · simp only [PNode.toVNodes]; rw [tv1, tv]

end Snabbdom
