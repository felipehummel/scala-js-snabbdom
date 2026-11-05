import Snabbdom.Proofs.Patch

namespace Snabbdom

theorem dn_eq (ex : DomNode) (A : String → Option String) (L L' : List NodeId) (h : L = L') :
    ({ { ex with attrs := A } with children := L } : DomNode) = { ex with attrs := A, children := L' } := by
  subst h; rfl

theorem dn_eq' (ex : DomNode) (A : String → Option String) (L : List NodeId) (h : ex.children = L) :
    ({ ex with attrs := A } : DomNode) = { ex with attrs := A, children := L } := by
  cases ex; simp only at h; subst h; rfl

theorem text_patched {d : Dom} {os s : String} {n : NodeId} (h : PPre d (.text os n)) :
    Patched d (.text os n) (.text s n) (if os ≠ s then d.setText n s else d) := by
  by_cases e : os = s
  · subst e; simp only [ne_eq, not_true_eq_false, ite_false]; exact Patched.refl h
  · rw [ite_eq_left e]
    obtain ⟨x, hx, hk, hc⟩ := h.mirrors
    rw [Dom.setText_text n s os x hx hk]
    refine ⟨Dom.modify_wf n _ (fun _ => ⟨rfl, rfl⟩) (Dom.log_wf _ h.wf), by simp, by simp, ?_,
      ⟨{ x with kind := .text s }, by simp [hx], rfl, hc⟩, by simp [PNode.ids], fun i hi => Or.inl hi, rfl, ?_⟩
    · intro i _ hi
      have : i ≠ n := fun e => hi (by simp [e, PNode.ids])
      simp [this]
    · intro y hy
      simp only [PNode.node] at hy ⊢
      rw [hx] at hy; cases hy
      exact ⟨{ x with kind := .text s }, by simp [hx], rfl⟩

theorem elem_patched {d d' : Dom} {osel : String} {odata data : Data} {oldCh newCh : List PNode}
    {elm : NodeId} (h : PPre d (.elem osel odata oldCh elm)) {ex : DomNode} (hex : d.nodes elm = some ex)
    (w : HeapWF d') (ok : d'.ok = d.ok) (le : d.next ≤ d'.next)
    (he' : d'.nodes elm = some { ex with attrs := renderAttrs osel data.attrs, children := newCh.map PNode.node })
    (fr : ∀ i, i < d.next → i ∉ (PNode.elem osel odata oldCh elm).ids → d'.nodes i = d.nodes i)
    (rp : MirrorsList d' newCh) (nd : (PNode.idsList newCh).Nodup)
    (rg : ∀ i ∈ PNode.idsList newCh, i ∈ PNode.idsList oldCh ∨ (d.next ≤ i ∧ i < d'.next)) :
    Patched d (.elem osel odata oldCh elm) (.elem osel data newCh elm) d' := by
  obtain ⟨x, hx, hk, _, _, _⟩ := h.mirrors
  rw [hex] at hx; cases hx
  have hnd := h.ids_nodup; rw [PNode.ids_elem, List.nodup_cons] at hnd
  have helm := h.ids_lt elm (by simp [PNode.ids])
  refine ⟨w, ok, le, fr, ⟨_, he', hk, rfl, rfl, rp⟩, ?_, ?_, rfl, ?_⟩
  · rw [PNode.ids_elem, List.nodup_cons]
    refine ⟨fun hm => ?_, nd⟩
    rcases rg elm hm with h1 | h1
    · exact hnd.1 h1
    · omega
  · intro i hi
    rw [PNode.ids_elem, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact Or.inl (by simp [PNode.ids])
    · rcases rg i hi with h1 | h1
      · exact Or.inl (by rw [PNode.ids_elem]; exact List.mem_cons_of_mem _ h1)
      · exact Or.inr h1
  · intro y hy
    simp only [PNode.node] at hy ⊢
    rw [hex] at hy; cases hy
    exact ⟨_, he', rfl⟩

theorem patch_elem (osel : String) (odata data : Data) (oldCh : List PNode) (elm : NodeId)
    (ch : List VNode) (d : Dom)
    (h : PPre d (.elem osel odata oldCh elm)) (hv : (VNode.elem osel data ch).WF)
    (heq : ¬ VNode.elem osel data ch = (PNode.elem osel odata oldCh elm).toVNode)
    (ihc : ∀ (oldCh : List PNode) (elm n0 : NodeId) (C : List NodeId) (byKey : String → List PNode)
      (pos : Nat) (d : Dom), MPre oldCh elm n0 C byKey pos d → VNode.WFs ch →
      MPost oldCh elm C pos ch d (matchChildren oldCh byKey pos ch d).1 (matchChildren oldCh byKey pos ch d).2) :
    Patched d (.elem osel odata oldCh elm)
        (patchVnode (.elem osel odata oldCh elm) (.elem osel data ch) d).1
        (patchVnode (.elem osel odata oldCh elm) (.elem osel data ch) d).2 ∧
      (patchVnode (.elem osel odata oldCh elm) (.elem osel data ch) d).1.toVNode = .elem osel data ch := by
  obtain ⟨hattrs, hch⟩ := hv
  have hwo := h.wf_old
  simp only [PNode.toVNode, VNode.WF] at hwo
  obtain ⟨ex, hex, hk, hea, hec, hrl⟩ := h.mirrors
  obtain ⟨g, hst, hg⟩ := moduleUpdate_step osel odata oldCh elm osel data ch d
  have hnd := h.ids_nodup; rw [PNode.ids_elem, List.nodup_cons] at hnd
  have helm : elm < d.next := h.ids_lt elm (by simp [PNode.ids])
  have hidl : ∀ i ∈ PNode.idsList oldCh, i < d.next := fun i hi =>
    h.ids_lt i (by rw [PNode.ids_elem]; exact List.mem_cons_of_mem _ hi)
  have hnot : ∀ i, i ∉ (PNode.elem osel odata oldCh elm).ids → i ≠ elm ∧ i ∉ PNode.idsList oldCh :=
    fun i hi => ⟨fun e => hi (by simp [e, PNode.ids]),
      fun hm => hi (by rw [PNode.ids_elem]; exact List.mem_cons_of_mem _ hm)⟩
  rw [patchVnode, ite_eq_right heq]
  generalize hd1 : moduleUpdate (.elem osel odata oldCh elm) (.elem osel data ch) d = d1 at hst
  have he1 : d1.nodes elm = some { ex with attrs := renderAttrs osel data.attrs } := by
    rw [hst.nodes, ite_eq_left rfl, hex]; simp [hea, hg hwo.1 hattrs]
  have fr1 : ∀ i, i ≠ elm → d1.nodes i = d.nodes i := fun i hi => hst.other i hi
  have w1 := hst.wf h.wf
  have rl1 : MirrorsList d1 oldCh := MirrorsList.frame oldCh hrl
    (fun i hi => SameContent.of_eq (fr1 i (fun e => hnd.1 (e ▸ hi))))
  have nx1 : d1.next = d.next := hst.next
  dsimp only
  cases oldCh with
  | nil =>
    cases ch with
    | nil =>
      dsimp only
      refine ⟨elem_patched h hex w1 hst.ok (by omega) ?_ (fun i _ hi => fr1 i (hnot i hi).1) trivial
        (by simp [PNode.idsList]) (by simp [PNode.idsList]), rfl⟩
      rw [he1, dn_eq' ex _ _ hec]
    | cons c cs =>
      dsimp only
      obtain ⟨w2, ok2, le2, ne2, fr2, rp2, nd2, rg2, tv2⟩ :=
        createAndInsert_spec elm (c :: cs) d1 _ w1 he1 (by omega) hch
      generalize createAndInsert elm (c :: cs) d1 = r at w2 ok2 le2 ne2 fr2 rp2 nd2 rg2 tv2 ⊢
      obtain ⟨ps, d2⟩ := r
      dsimp only at *
      refine ⟨elem_patched h hex w2 (by rw [ok2, hst.ok]) (by omega) ?_ ?_ rp2 nd2 ?_, ?_⟩
      · rw [ne2, hec]; rfl
      · intro i hi hio
        rw [fr2 i (by omega) (hnot i hio).1, fr1 i (hnot i hio).1]
      · intro i hi; exact Or.inr ⟨by have := (rg2 i hi).1; omega, (rg2 i hi).2⟩
      · simp only [PNode.toVNode, tv2]
  | cons o os =>
    cases ch with
    | nil =>
      dsimp only
      have hnd' := PNode.roots_nodup _ hnd.2
      obtain ⟨w2, ok2, nx2, ne2, _, fr2⟩ := removeAll_spec elm (o :: os) d1 _ w1 he1 hnd'
        (fun o' ho' => ⟨by rw [hec]; exact List.mem_map_of_mem ho',
          fun e => hnd.1 (e ▸ PNode.mem_ids_of_mem ho' (PNode.node_mem_ids o'))⟩)
      refine ⟨elem_patched h hex w2 (by rw [ok2, hst.ok]) (by omega) ?_ ?_ trivial
        (by simp [PNode.idsList]) (by simp [PNode.idsList]), rfl⟩
      · rw [ne2]
        congr 2
        rw [hec]
        exact List.filter_eq_nil_iff.2 (fun x hx => by rw [decide_eq_true_eq]; exact fun hn => hn hx)
      · intro i _ hio
        have hm : i ∉ (o :: os).map PNode.node := by
          intro hm; obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hm
          exact (hnot _ hio).2 (PNode.mem_ids_of_mem ho' (PNode.node_mem_ids o'))
        rw [fr2 i (hnot i hio).1 hm, fr1 i (hnot i hio).1]
    | cons c cs =>
      dsimp only
      by_cases hsame : PNode.toVNodes (o :: os) = c :: cs
      · rw [ite_eq_right (fun h' => h' hsame)]
        dsimp only
        refine ⟨elem_patched h hex w1 hst.ok (by omega) ?_ (fun i _ hi => fr1 i (hnot i hi).1) rl1 hnd.2
          (fun i hi => Or.inl hi), ?_⟩
        · rw [he1, dn_eq' ex _ _ hec]
        · simp only [PNode.toVNode, hsame]
      · rw [ite_eq_left hsame]
        have hpre : MPre (o :: os) elm d1.next [] (keyedOld (o :: os)) 0 d1 := by
          refine ⟨w1, hnd.2, fun i hi => by rw [nx1]; exact hidl i hi, by rw [nx1]; exact helm, hnd.1,
            Nat.le_refl _, fun o' ho' => WFs_mem hwo.2 ho', ?_, ?_, ?_, ?_⟩
          · intro o' ho' _
            refine ⟨MirrorsList.mem rl1 ho', ?_⟩
            have hm : o'.node ∈ ex.children := by rw [hec]; exact List.mem_map_of_mem ho'
            obtain ⟨y, hy, hyp⟩ := h.wf.child_parent elm ex o'.node hex hm
            have hne : o'.node ≠ elm := fun e => hnd.1 (e ▸ PNode.mem_ids_of_mem ho' (PNode.node_mem_ids o'))
            exact ⟨y, by rw [fr1 _ hne]; exact hy, hyp⟩
          · intro k o' ho'
            obtain ⟨h1, h2⟩ := List.mem_filter.1 ho'
            exact ⟨h1, by simpa using h2, by simp⟩
          · intro k
            exact List.Nodup.sublist (List.filter_sublist.map PNode.node) (PNode.roots_nodup _ hnd.2)
          · intro _ _ _ _ _; simp
        have hmp := ihc (o :: os) elm d1.next [] (keyedOld (o :: os)) 0 d1 hpre hch
        generalize matchChildren (o :: os) (keyedOld (o :: os)) 0 (c :: cs) d1 = r at hmp ⊢
        obtain ⟨pls, d2⟩ := r
        dsimp only at hmp ⊢
        obtain ⟨w4, ok4, le4, hr4, ne4, fr4, rp4⟩ := finish_spec hpre hmp he1 hec
        generalize finishChildren elm (o :: os) pls d2 = r at w4 ok4 le4 hr4 ne4 fr4 rp4 ⊢
        obtain ⟨pch, d4⟩ := r
        dsimp only at *
        subst hr4
        have := hmp.le
        refine ⟨elem_patched h hex w4 (by rw [ok4, hst.ok]) (by omega) ?_ ?_ rp4 hmp.ids_nodup ?_, ?_⟩
        · rw [ne4, List.map_map]; rfl
        · intro i hi hio
          rw [fr4 i (by omega) (hnot i hio).2 (hnot i hio).1, fr1 i (hnot i hio).1]
        · intro i hi
          rcases hmp.ids_range i hi with hc | hc
          · exact Or.inl hc.mem
          · exact Or.inr ⟨by omega, by rw [le4]; exact hc.2⟩
        · simp only [PNode.toVNode, hmp.toV]

mutual
theorem patchVnode_spec : ∀ (v : VNode) (old : PNode) (d : Dom), PPre d old → v.WF →
    sameVnode old v = true →
    Patched d old (patchVnode old v d).1 (patchVnode old v d).2 ∧ (patchVnode old v d).1.toVNode = v
  | .text s, old, d, h, _, hs => by
    by_cases heq : VNode.text s = old.toVNode
    · rw [patchVnode, ite_eq_left heq]; exact ⟨Patched.refl h, heq.symm⟩
    · cases old with
      | text os n =>
        rw [patchVnode, ite_eq_right heq]
        exact ⟨text_patched h, rfl⟩
      | comment _ _ => simp [sameVnode] at hs
      | elem _ _ _ _ => simp [sameVnode] at hs
  | .comment s, old, d, _, _, hs => by cases old <;> simp [sameVnode] at hs
  | .elem sel data ch, old, d, h, hv, hs => by
    have ihc := matchChildren_spec ch
    by_cases heq : VNode.elem sel data ch = old.toVNode
    · rw [patchVnode, ite_eq_left heq]; exact ⟨Patched.refl h, heq.symm⟩
    · cases old with
      | text _ _ => simp [sameVnode] at hs
      | comment _ _ => simp [sameVnode] at hs
      | elem osel odata oldCh elm =>
        have e := sameVnode_sel hs
        subst e
        exact patch_elem osel odata data oldCh elm ch d h hv heq ihc

theorem matchChildren_spec : ∀ (vs : List VNode) (oldCh : List PNode) (elm n0 : NodeId)
    (C : List NodeId) (byKey : String → List PNode) (pos : Nat) (d : Dom),
    MPre oldCh elm n0 C byKey pos d → VNode.WFs vs →
    MPost oldCh elm C pos vs d (matchChildren oldCh byKey pos vs d).1 (matchChildren oldCh byKey pos vs d).2
  | [], oldCh, elm, n0, C, byKey, pos, d, h, _ => by
    simp only [matchChildren]; exact mpost_nil h.wf
  | v :: vs, oldCh, elm, n0, C, byKey, pos, d, h, hv => by
    have ihp := patchVnode_spec v
    have ihs := matchChildren_spec vs
    obtain ⟨C', hs, h1⟩ := matchOne_spec oldCh elm n0 C byKey pos v (fun o d => patchVnode o v d) d h hv.1
      (fun o ho hoC hsv => ihp o d (h.ppre ho hoC) hv.1 hsv)
    generalize hm : matchOne oldCh byKey pos v (fun o d => patchVnode o v d) d = m at hs h1
    obtain ⟨pl, byKey', d1⟩ := m
    have hr := ihs oldCh elm n0 C' byKey' (pos + 1) d1 h1 hv.2
    generalize hr2 : matchChildren oldCh byKey' (pos + 1) vs d1 = r at hr
    obtain ⟨pls, d2⟩ := r
    have he : matchChildren oldCh byKey pos (v :: vs) d = (pl :: pls, d2) := by
      simp only [matchChildren, hm, hr2]
    rw [he]
    exact mpost_cons h hs hr
end

end Snabbdom
