import Snabbdom.Proofs.Attrs

namespace Snabbdom

def DomNode.content (x : DomNode) : Kind × (String → Option String) × List NodeId :=
  (x.kind, x.attrs, x.children)

/-- Node `i` looks the same to `Mirrors` in `d` and `d'`; its parent may differ. -/
def SameContent (d d' : Dom) (i : NodeId) : Prop :=
  (d'.nodes i).map DomNode.content = (d.nodes i).map DomNode.content

theorem SameContent.of_eq {d d' : Dom} {i : NodeId} (h : d'.nodes i = d.nodes i) :
    SameContent d d' i := by unfold SameContent; rw [h]

theorem SameContent.trans {d1 d2 d3 : Dom} {i : NodeId} (h1 : SameContent d1 d2 i)
    (h2 : SameContent d2 d3 i) : SameContent d1 d3 i := by
  unfold SameContent at *; rw [h2, h1]

theorem SameContent.get {d d' : Dom} {i : NodeId} {x : DomNode} (h : SameContent d d' i)
    (hx : d.nodes i = some x) :
    ∃ x', d'.nodes i = some x' ∧ x'.kind = x.kind ∧ x'.attrs = x.attrs ∧ x'.children = x.children := by
  unfold SameContent at h; rw [hx] at h
  cases h' : d'.nodes i with
  | none => rw [h'] at h; cases h
  | some x' =>
    rw [h'] at h; simp only [Option.map_some, Option.some.injEq, DomNode.content, Prod.mk.injEq] at h
    exact ⟨x', rfl, h.1, h.2.1, h.2.2⟩

theorem PNode.node_mem_ids (p : PNode) : p.node ∈ p.ids := by
  cases p <;> simp [PNode.ids, PNode.node]

theorem PNode.idsList_cons (p : PNode) (ps : List PNode) :
    PNode.idsList (p :: ps) = p.ids ++ PNode.idsList ps := by simp [PNode.idsList]

theorem PNode.mem_idsList {ps : List PNode} {i : NodeId} :
    i ∈ PNode.idsList ps ↔ ∃ p ∈ ps, i ∈ p.ids := by
  induction ps with
  | nil => simp [PNode.idsList]
  | cons p ps ih => simp [PNode.idsList, ih]

theorem PNode.ids_elem (sel : String) (data : Data) (ch : List PNode) (n : NodeId) :
    (PNode.elem sel data ch n).ids = n :: PNode.idsList ch := by simp [PNode.ids]

mutual
theorem Mirrors.frame : ∀ (p : PNode) {d d' : Dom}, Mirrors d p →
    (∀ i ∈ p.ids, SameContent d d' i) → Mirrors d' p
  | .text s n, d, d', h, hs => by
    obtain ⟨x, hx, hk, hc⟩ := h
    obtain ⟨x', hx', hk', _, hc'⟩ := (hs n (by simp [PNode.ids])).get hx
    exact ⟨x', hx', hk' ▸ hk, hc' ▸ hc⟩
  | .comment s n, d, d', h, hs => by
    obtain ⟨x, hx, hk, hc⟩ := h
    obtain ⟨x', hx', hk', _, hc'⟩ := (hs n (by simp [PNode.ids])).get hx
    exact ⟨x', hx', hk' ▸ hk, hc' ▸ hc⟩
  | .elem sel data ch n, d, d', h, hs => by
    obtain ⟨x, hx, hk, ha, hc, hl⟩ := h
    obtain ⟨x', hx', hk', ha', hc'⟩ := (hs n (by simp [PNode.ids])).get hx
    exact ⟨x', hx', hk' ▸ hk, ha' ▸ ha, hc' ▸ hc,
      MirrorsList.frame ch hl (fun i hi => hs i (by simp [PNode.ids, hi]))⟩
theorem MirrorsList.frame : ∀ (ps : List PNode) {d d' : Dom}, MirrorsList d ps →
    (∀ i ∈ PNode.idsList ps, SameContent d d' i) → MirrorsList d' ps
  | [], _, _, _, _ => trivial
  | p :: ps, d, d', h, hs =>
    ⟨Mirrors.frame p h.1 (fun i hi => hs i (by simp [PNode.idsList, hi])),
     MirrorsList.frame ps h.2 (fun i hi => hs i (by simp [PNode.idsList, hi]))⟩
end

mutual
theorem Mirrors.shows : ∀ (p : PNode) {d : Dom}, Mirrors d p → Shows d p.node p.toVNode.render
  | .text s n, d, h => by simpa [PNode.toVNode, VNode.render, Shows, PNode.node, Mirrors] using h
  | .comment s n, d, h => by simpa [PNode.toVNode, VNode.render, Shows, PNode.node, Mirrors] using h
  | .elem sel data ch n, d, h => by
    obtain ⟨x, hx, hk, ha, hc, hl⟩ := h
    simp only [PNode.toVNode, VNode.render, Shows, PNode.node]
    exact ⟨x, hx, hk, ha, hc ▸ MirrorsList.shows ch hl⟩
theorem MirrorsList.shows : ∀ (ps : List PNode) {d : Dom}, MirrorsList d ps →
    ShowsList d (ps.map PNode.node) (VNode.renders (PNode.toVNodes ps))
  | [], _, _ => by simp [PNode.toVNodes, VNode.renders, ShowsList]
  | p :: ps, d, h => by
    simp only [List.map_cons, PNode.toVNodes, VNode.renders, ShowsList]
    exact ⟨Mirrors.shows p h.1, MirrorsList.shows ps h.2⟩
end

theorem appendAll_spec (n : NodeId) : ∀ (cs : List PNode) (d : Dom) (nx : DomNode),
    HeapWF d → d.nodes n = some nx →
    (cs.map PNode.node).Nodup →
    (∀ c ∈ cs, c.node ≠ n ∧ ∃ cx, d.nodes c.node = some cx ∧ cx.parent = none) →
    let d' := appendAll n cs d
    HeapWF d' ∧ d'.ok = d.ok ∧ d'.next = d.next ∧
    (∀ m, d'.nodes m =
      if m = n then some { nx with children := nx.children ++ cs.map PNode.node }
      else if m ∈ cs.map PNode.node then (d.nodes m).map (fun x => { x with parent := some n })
      else d.nodes m)
  | [], d, nx, hw, hn, _, _ => by
    refine ⟨hw, rfl, rfl, fun m => ?_⟩
    simp only [appendAll, List.map_nil, List.append_nil, List.not_mem_nil, ite_false]
    split
    · subst m; rw [hn]
    · rfl
  | c :: cs, d, nx, hw, hn, hnd, hcs => by
    obtain ⟨hcn, cx, hcx, hcp⟩ := hcs c List.mem_cons_self
    have hi : Dom.InsertOk (d.log (.appendChild n c.node)) n c.node none nx cx :=
      ⟨hn, hcx, hcn, Or.inl hcp, fun r h => by cases h⟩
    have hwl := Dom.log_wf (.appendChild n c.node) hw
    have hN := Dom.preInsert_nodes hwl hi
    have hnot := hi.not_mem hwl hcp
    have hw1 := Dom.preInsert_wf hwl hi
    have hok1 := Dom.preInsert_ok hi
    let d1 := d.appendChild n c.node
    have hd1 : d1 = (d.log (.appendChild n c.node)).preInsert n c.node none := rfl
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hn1 : d1.nodes n = some { nx with children := nx.children ++ [c.node] } := by
      rw [hd1, hN]; simp [insertAt, List.erase_of_not_mem hnot]
    have ih := appendAll_spec n cs d1 _ (hd1 ▸ hw1) hn1 hnd.2 (by
      intro c' hc'
      obtain ⟨hne, cx', hcx', hcp'⟩ := hcs c' (List.mem_cons_of_mem _ hc')
      refine ⟨hne, cx', ?_, hcp'⟩
      have : c'.node ≠ c.node := fun e => hnd.1 (e ▸ List.mem_map_of_mem hc')
      rw [hd1, hN]; simp [hne, this, hcx'])
    obtain ⟨w', ok', next', nodes'⟩ := ih
    simp only [appendAll]
    refine ⟨w', by rw [ok', hd1, hok1]; rfl, by rw [next', hd1]; simp, fun m => ?_⟩
    rw [nodes']
    by_cases hm : m = n
    · simp [hm]
    · simp only [hm, ite_false, List.map_cons, List.mem_cons]
      by_cases hmc : m = c.node
      · subst hmc
        simp only [true_or, ite_true]
        have : c.node ∉ cs.map PNode.node := hnd.1
        simp only [this, ite_false]
        rw [hd1, hN]; simp [hm, hcx]
      · simp only [hmc, false_or]
        split
        · rw [hd1, hN]; simp [hm, hmc]
        · rw [hd1, hN]; simp [hm, hmc]

structure Created (d : Dom) (c : PNode) (d' : Dom) : Prop where
  wf : HeapWF d'
  ok : d'.ok = d.ok
  le : d.next ≤ d'.next
  frame : ∀ i, i < d.next → d'.nodes i = d.nodes i
  mirrors : Mirrors d' c
  ids_nodup : c.ids.Nodup
  ids_range : ∀ i ∈ c.ids, d.next ≤ i ∧ i < d'.next
  detached : ∃ x, d'.nodes c.node = some x ∧ x.parent = none

structure CreatedList (d : Dom) (cs : List PNode) (d' : Dom) : Prop where
  wf : HeapWF d'
  ok : d'.ok = d.ok
  le : d.next ≤ d'.next
  frame : ∀ i, i < d.next → d'.nodes i = d.nodes i
  mirrors : MirrorsList d' cs
  ids_nodup : (PNode.idsList cs).Nodup
  ids_range : ∀ i ∈ PNode.idsList cs, d.next ≤ i ∧ i < d'.next
  detached : ∀ c ∈ cs, ∃ x, d'.nodes c.node = some x ∧ x.parent = none

theorem CreatedList.roots_nodup {d d' : Dom} {cs : List PNode} (h : CreatedList d cs d') :
    (cs.map PNode.node).Nodup := by
  have hn := h.ids_nodup
  clear h
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [PNode.idsList_cons, List.nodup_append] at hn
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hn.2.1⟩
    obtain ⟨c', hc', he⟩ := List.mem_map.1 hm
    exact hn.2.2 c.node (PNode.node_mem_ids c) c.node
      (PNode.mem_idsList.2 ⟨c', hc', he ▸ PNode.node_mem_ids c'⟩) rfl

theorem createNode_spec (d : Dom) (k : Kind) (hw : HeapWF d) :
    let r := d.alloc k
    r.1 = d.next ∧ HeapWF r.2 ∧ r.2.ok = d.ok ∧ r.2.next = d.next + 1 ∧
    r.2.nodes d.next = some { kind := k } ∧ (∀ i, i < d.next → r.2.nodes i = d.nodes i) :=
  ⟨rfl, Dom.alloc_wf k hw, rfl, rfl, by simp [Dom.alloc_nodes], fun i hi => Dom.alloc_nodes_old k i hi⟩

mutual
theorem createElm_spec : ∀ (v : VNode) (d : Dom), HeapWF d → v.WF →
    Created d (createElm v d).1 (createElm v d).2 ∧ (createElm v d).1.toVNode = v
  | .text s, d, hw, _ => by
    obtain ⟨_, w1, ok1, nx1, nd1, fr1⟩ := createNode_spec d (.text s) hw
    simp only [createElm, Dom.createText]
    refine ⟨⟨Dom.log_wf _ w1, ok1, by simp, fr1, ⟨_, nd1, rfl, rfl⟩, by simp [PNode.ids],
      by simp [PNode.ids, Dom.alloc_fst], ⟨_, by simpa [PNode.node, Dom.alloc_fst] using nd1, rfl⟩⟩,
      rfl⟩
  | .comment s, d, hw, _ => by
    obtain ⟨_, w1, ok1, nx1, nd1, fr1⟩ := createNode_spec d (.comment s) hw
    simp only [createElm, Dom.createComment]
    refine ⟨⟨Dom.log_wf _ w1, ok1, by simp, fr1, ⟨_, nd1, rfl, rfl⟩, by simp [PNode.ids],
      by simp [PNode.ids, Dom.alloc_fst], ⟨_, by simpa [PNode.node, Dom.alloc_fst] using nd1, rfl⟩⟩,
      rfl⟩
  | .elem sel data ch, d, hw, hv => by
    obtain ⟨_, hattrs, hch⟩ := hv
    let raw := (Selector.parse sel).tag
    let tag := asciiLower raw
    obtain ⟨_, w1, ok1, nx1, nd1, fr1⟩ := createNode_spec d (.elem tag) hw
    have w1' := Dom.log_wf (.createElement d.next raw) w1
    obtain ⟨cl, htv⟩ := createElms_spec ch _ w1' hch
    generalize hr : createElms ch ((d.alloc (.elem tag)).2.log (.createElement d.next raw)) = r at cl htv
    obtain ⟨pch, d2⟩ := r
    simp only at cl htv
    have le2 : d.next + 1 ≤ d2.next := by have := cl.le; simpa using this
    have range2 : ∀ i ∈ PNode.idsList pch, d.next + 1 ≤ i ∧ i < d2.next := by
      intro i hi; have := cl.ids_range i hi; simpa using this
    have frame2 : ∀ i, i < d.next + 1 → d2.nodes i = (d.alloc (.elem tag)).2.nodes i := by
      intro i hi; have := cl.frame i (by simpa using hi); simpa using this
    have hd : createElm (.elem sel data ch) d = (.elem sel data pch d.next,
        appendAll d.next pch (moduleCreate (.elem sel data pch d.next)
          (setSelectorAttrs d.next (Selector.parse sel) d2))) := by
      simp only [createElm, Dom.createElement, Dom.alloc_fst, hr, tag, raw]
    obtain ⟨gs, sts, hgs⟩ := setSelectorAttrs_step d.next (Selector.parse sel) d2
    have st3 := sts.trans (moduleCreate_step sel data pch d.next _)
    generalize hd3 : moduleCreate (.elem sel data pch d.next)
      (setSelectorAttrs d.next (Selector.parse sel) d2) = d3 at hd st3
    rw [hd]
    have w3 := st3.wf cl.wf
    have hn2 : d2.nodes d.next = some { kind := .elem tag } := by
      rw [frame2 d.next (by omega)]; exact nd1
    have hn3 : d3.nodes d.next = some { kind := .elem tag, attrs := renderAttrs sel data.attrs } := by
      rw [st3.nodes, ite_eq_left rfl, hn2]
      simp [hgs, setAll_selector sel _ hattrs]
    have hroots : ∀ c ∈ pch, c.node ≠ d.next ∧ ∃ cx, d3.nodes c.node = some cx ∧ cx.parent = none := by
      intro c hc
      have hr := range2 c.node (PNode.mem_idsList.2 ⟨c, hc, PNode.node_mem_ids c⟩)
      have hne : c.node ≠ d.next := by omega
      refine ⟨hne, ?_⟩
      rw [st3.other _ hne]; exact cl.detached c hc
    obtain ⟨w4, ok4, next4, nodes4⟩ :=
      appendAll_spec d.next pch d3 _ w3 hn3 cl.roots_nodup hroots
    refine ⟨⟨w4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ok4, st3.ok, cl.ok]; simp
    · rw [next4, st3.next]; omega
    · intro i hi
      have hin : i ≠ d.next := by omega
      rw [nodes4, ite_eq_right hin]
      have hnot : i ∉ pch.map PNode.node := by
        intro hm; obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
        have := range2 c.node (PNode.mem_idsList.2 ⟨c, hc, PNode.node_mem_ids c⟩)
        omega
      rw [ite_eq_right hnot, st3.other _ hin, frame2 i (by omega)]
      exact fr1 i hi
    · refine ⟨_, by rw [nodes4, ite_eq_left rfl], rfl, rfl, by simp, ?_⟩
      refine MirrorsList.frame pch cl.mirrors (fun i hi => ?_)
      have hr := range2 i hi
      have hin : i ≠ d.next := by omega
      unfold SameContent
      rw [nodes4, ite_eq_right hin, st3.other _ hin]
      split
      · cases d2.nodes i <;> rfl
      · rfl
    · rw [PNode.ids_elem, List.nodup_cons]
      refine ⟨fun hm => ?_, cl.ids_nodup⟩
      have := range2 d.next hm; omega
    · intro i hi
      rw [PNode.ids_elem, List.mem_cons] at hi
      rw [next4, st3.next]
      rcases hi with rfl | hi
      · omega
      · have := range2 i hi; omega
    · refine ⟨_, by simp only [PNode.node]; rw [nodes4, ite_eq_left rfl], rfl⟩
    · simp only [PNode.toVNode]; rw [htv]
theorem createElms_spec : ∀ (vs : List VNode) (d : Dom), HeapWF d → VNode.WFs vs →
    CreatedList d (createElms vs d).1 (createElms vs d).2 ∧
      PNode.toVNodes (createElms vs d).1 = vs
  | [], d, hw, _ => by
    simp only [createElms]
    exact ⟨⟨hw, rfl, Nat.le_refl _, fun _ _ => rfl, trivial, by simp [PNode.idsList],
      by simp [PNode.idsList], by simp⟩, rfl⟩
  | v :: vs, d, hw, hv => by
    obtain ⟨c1, tv1⟩ := createElm_spec v d hw hv.1
    generalize hr1 : createElm v d = r1 at c1 tv1
    obtain ⟨c, d1⟩ := r1
    simp only at c1 tv1
    obtain ⟨cl, tvs⟩ := createElms_spec vs d1 c1.wf hv.2
    generalize hr2 : createElms vs d1 = r2 at cl tvs
    obtain ⟨cs, d2⟩ := r2
    simp only at cl tvs
    have hd : createElms (v :: vs) d = (c :: cs, d2) := by
      simp only [createElms, hr1, hr2]
    rw [hd]
    show CreatedList d (c :: cs) d2 ∧ PNode.toVNodes (c :: cs) = v :: vs
    refine ⟨⟨cl.wf, by rw [cl.ok, c1.ok], by have := cl.le; have := c1.le; omega,
      fun i hi => by rw [cl.frame i (by have := c1.le; omega), c1.frame i hi], ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact ⟨Mirrors.frame c c1.mirrors (fun i hi => SameContent.of_eq (cl.frame i (c1.ids_range i hi).2)),
        cl.mirrors⟩
    · rw [PNode.idsList_cons, List.nodup_append]
      refine ⟨c1.ids_nodup, cl.ids_nodup, fun a ha b hb e => ?_⟩
      subst e
      have := (c1.ids_range a ha).2; have := (cl.ids_range a hb).1; omega
    · intro i hi
      rw [PNode.idsList_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · have := c1.ids_range i hi; have := cl.le; omega
      · have := cl.ids_range i hi; have := c1.le; omega
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · obtain ⟨x, hx, hp⟩ := c1.detached
        refine ⟨x, ?_, hp⟩
        rw [cl.frame _ (c1.ids_range _ (PNode.node_mem_ids _)).2]; exact hx
      · exact cl.detached c' hc'
    · simp only [PNode.toVNodes]; rw [tv1, tvs]
end

theorem createElm_shows (v : VNode) (d : Dom) (hw : HeapWF d) (hv : v.WF) :
    Shows (createElm v d).2 (createElm v d).1.node v.render := by
  obtain ⟨c, tv⟩ := createElm_spec v d hw hv
  have := Mirrors.shows _ c.mirrors
  rwa [tv] at this

/-- Mounting gives `patch` a valid input, and by `patch_correct` so does every
patch after it. -/
theorem createElm_valid (v : VNode) (d : Dom) (hw : HeapWF d) (hok : d.ok = true) (hv : v.WF) :
    Valid (createElm v d).2 (createElm v d).1 := by
  obtain ⟨c, tv⟩ := createElm_spec v d hw hv
  exact ⟨⟨c.wf, c.mirrors, c.ids_nodup, fun i hi => (c.ids_range i hi).2, by rw [tv]; exact hv⟩,
    by rw [c.ok, hok]⟩

end Snabbdom
