/-
The matching fold's invariant `MPre` tracks which old children have been
claimed so far (`C`): a claimed child's subtree is being rewritten by the
recursive `patchVnode`, so the fold may no longer assume it mirrors the DOM,
and no later new child may claim it again.
-/
import Snabbdom.Proofs.PlaceFewest

namespace Snabbdom

structure Patched (d : Dom) (old c : PNode) (d' : Dom) : Prop where
  wf : HeapWF d'
  ok : d'.ok = d.ok
  le : d.next ≤ d'.next
  frame : ∀ i, i < d.next → i ∉ old.ids → d'.nodes i = d.nodes i
  mirrors : Mirrors d' c
  ids_nodup : c.ids.Nodup
  ids_range : ∀ i ∈ c.ids, i ∈ old.ids ∨ (d.next ≤ i ∧ i < d'.next)
  node : c.node = old.node
  parent : ∀ x, d.nodes old.node = some x → ∃ x', d'.nodes old.node = some x' ∧ x'.parent = x.parent

theorem Patched.refl {d : Dom} {old : PNode} (h : PPre d old) : Patched d old old d :=
  ⟨h.wf, rfl, Nat.le_refl _, fun _ _ _ => rfl, h.mirrors, h.ids_nodup, fun _ hi => Or.inl hi, rfl,
    fun x hx => ⟨x, hx, rfl⟩⟩

def InClaimed (oldCh : List PNode) (N : List NodeId) (i : NodeId) : Prop :=
  ∃ o ∈ oldCh, o.node ∈ N ∧ i ∈ o.ids

theorem InClaimed.cons {oldCh : List PNode} {N : List NodeId} {i : NodeId} (a : NodeId)
    (h : InClaimed oldCh N i) : InClaimed oldCh (a :: N) i :=
  let ⟨o, ho, hN, hi⟩ := h; ⟨o, ho, List.mem_cons_of_mem _ hN, hi⟩

theorem InClaimed.mem {oldCh : List PNode} {N : List NodeId} {i : NodeId}
    (h : InClaimed oldCh N i) : i ∈ PNode.idsList oldCh :=
  let ⟨_, ho, _, hi⟩ := h; PNode.mem_ids_of_mem ho hi

/-- Invariant of the matching fold over the children of `elm`. `C` holds the
roots of the old children claimed so far; `n0` bounds the old ids. -/
structure MPre (oldCh : List PNode) (elm n0 : NodeId) (C : List NodeId)
    (byKey : String → List PNode) (pos : Nat) (d : Dom) : Prop where
  wf : HeapWF d
  ids_nodup : (PNode.idsList oldCh).Nodup
  ids_lt : ∀ i ∈ PNode.idsList oldCh, i < n0
  elm_lt : elm < n0
  elm_not : elm ∉ PNode.idsList oldCh
  n0_le : n0 ≤ d.next
  wf_old : ∀ o ∈ oldCh, o.toVNode.WF
  avail : ∀ o ∈ oldCh, o.node ∉ C → Mirrors d o ∧ ∃ x, d.nodes o.node = some x ∧ x.parent = some elm
  bykey : ∀ k, ∀ o ∈ byKey k, o ∈ oldCh ∧ o.key = some k ∧ o.node ∉ C
  bykey_nodup : ∀ k, ((byKey k).map PNode.node).Nodup
  unkeyed : ∀ i o, pos ≤ i → oldCh[i]? = some o → o.key = none → o.node ∉ C

/-- What the fold returns. -/
structure MPost (oldCh : List PNode) (elm : NodeId) (C : List NodeId) (pos : Nat)
    (vs : List VNode) (d : Dom) (pls : List Placement) (d' : Dom) : Prop where
  wf : HeapWF d'
  ok : d'.ok = d.ok
  le : d.next ≤ d'.next
  frame : ∀ i, i < d.next → ¬ InClaimed oldCh (pls.map (·.child.node)) i → d'.nodes i = d.nodes i
  mirrors : MirrorsList d' (pls.map (·.child))
  toV : PNode.toVNodes (pls.map (·.child)) = vs
  ids_nodup : (PNode.idsList (pls.map (·.child))).Nodup
  ids_range : ∀ i ∈ PNode.idsList (pls.map (·.child)),
    InClaimed oldCh (pls.map (·.child.node)) i ∨ (d.next ≤ i ∧ i < d'.next)
  roots : ∀ pl ∈ pls, (∃ o ∈ oldCh, o.node ∉ C ∧ pl.child.node = o.node) ∨
    (d.next ≤ pl.child.node ∧ pl.child.node < d'.next)
  roots_nodup : (pls.map (·.child.node)).Nodup
  anchored_at : ∀ (i : Nat) (c : NodeId), (pls.map Placement.toPair)[i]? = some (true, c) →
    (oldCh.map PNode.node)[pos + i]? = some c
  parent : ∀ pl ∈ pls, ∃ x, d'.nodes pl.child.node = some x ∧ (x.parent = none ∨ x.parent = some elm)

/-- One step of the fold: `pl` either claims the old child `o`, or is new. -/
structure Step (oldCh : List PNode) (elm : NodeId) (C : List NodeId) (pos : Nat) (v : VNode)
    (d : Dom) (pl : Placement) (d1 : Dom) (C' : List NodeId) : Prop where
  ok : d1.ok = d.ok
  le : d.next ≤ d1.next
  mirrors : Mirrors d1 pl.child
  ids_nodup : pl.child.ids.Nodup
  toV : pl.child.toVNode = v
  parent : ∃ x, d1.nodes pl.child.node = some x ∧ (x.parent = none ∨ x.parent = some elm)
  kind : (∃ o ∈ oldCh, o.node ∉ C ∧ C' = o.node :: C ∧ pl.child.node = o.node ∧
      (∀ i, i < d.next → i ∉ o.ids → d1.nodes i = d.nodes i) ∧
      (∀ i ∈ pl.child.ids, i ∈ o.ids ∨ (d.next ≤ i ∧ i < d1.next)) ∧
      (pl.toPair.1 = true → oldCh[pos]? = some o)) ∨
    (C' = C ∧ pl.toPair.1 = false ∧ (∀ i, i < d.next → d1.nodes i = d.nodes i) ∧
      (∀ i ∈ pl.child.ids, d.next ≤ i ∧ i < d1.next))

theorem PNode.ids_nodup_of_mem : ∀ {L : List PNode} {o : PNode}, o ∈ L → (PNode.idsList L).Nodup → o.ids.Nodup
  | [], _, ho, _ => by cases ho
  | a :: L, o, ho, hn => by
    rw [PNode.idsList_cons, List.nodup_append] at hn
    rcases List.mem_cons.1 ho with rfl | ho
    · exact hn.1
    · exact PNode.ids_nodup_of_mem ho hn.2.1

theorem MirrorsList.mem : ∀ {d : Dom} {L : List PNode} {o : PNode}, MirrorsList d L → o ∈ L → Mirrors d o
  | _, [], _, _, ho => by cases ho
  | _, a :: L, o, h, ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact h.1
    · exact MirrorsList.mem h.2 ho

theorem WFs_mem : ∀ {L : List PNode} {o : PNode}, VNode.WFs (PNode.toVNodes L) → o ∈ L → o.toVNode.WF
  | [], _, _, ho => by cases ho
  | a :: L, o, h, ho => by
    simp only [PNode.toVNodes, VNode.WFs] at h
    rcases List.mem_cons.1 ho with rfl | ho
    · exact h.1
    · exact WFs_mem h.2 ho

theorem MPre.ppre {oldCh elm n0 C byKey pos d} (h : MPre oldCh elm n0 C byKey pos d) {o : PNode}
    (ho : o ∈ oldCh) (hoC : o.node ∉ C) : PPre d o :=
  ⟨h.wf, (h.avail o ho hoC).1, PNode.ids_nodup_of_mem ho h.ids_nodup,
    fun i hi => by have := h.ids_lt i (PNode.mem_ids_of_mem ho hi); have := h.n0_le; omega,
    h.wf_old o ho⟩

theorem step_claim {oldCh elm n0 C byKey pos v d} (h : MPre oldCh elm n0 C byKey pos d)
    {o c : PNode} {d1 : Dom} {byKey' : String → List PNode} (pl : Placement)
    (ho : o ∈ oldCh) (hoC : o.node ∉ C) (hP : Patched d o c d1) (htv : c.toVNode = v)
    (hpl : pl.child = c) (hanch : pl.toPair.1 = true → oldCh[pos]? = some o)
    (hbk : ∀ k, ∀ o' ∈ byKey' k, o' ∈ oldCh ∧ o'.key = some k ∧ o'.node ∉ o.node :: C)
    (hbkn : ∀ k, ((byKey' k).map PNode.node).Nodup)
    (hunk : ∀ i o', pos + 1 ≤ i → oldCh[i]? = some o' → o'.key = none → o'.node ≠ o.node) :
    Step oldCh elm C pos v d pl d1 (o.node :: C) ∧ MPre oldCh elm n0 (o.node :: C) byKey' (pos + 1) d1 := by
  subst hpl
  obtain ⟨_, x, hx, hxp⟩ := h.avail o ho hoC
  obtain ⟨x', hx', hxp'⟩ := hP.parent x hx
  refine ⟨⟨hP.ok, hP.le, hP.mirrors, hP.ids_nodup, htv,
    ⟨x', by rw [hP.node]; exact hx', Or.inr (hxp'.trans hxp)⟩,
    Or.inl ⟨o, ho, hoC, rfl, hP.node, hP.frame, hP.ids_range, hanch⟩⟩, ?_⟩
  have hle := hP.le; have hn0 := h.n0_le
  refine ⟨hP.wf, h.ids_nodup, h.ids_lt, h.elm_lt, h.elm_not, by omega, h.wf_old, ?_, hbk, hbkn, ?_⟩
  · intro o' ho' hC
    simp only [List.mem_cons, not_or] at hC
    obtain ⟨hr', y, hy, hyp⟩ := h.avail o' ho' hC.2
    have hfr : ∀ i ∈ o'.ids, d1.nodes i = d.nodes i := fun i hi => hP.frame i
      (by have := h.ids_lt i (PNode.mem_ids_of_mem ho' hi); omega)
      (fun hio => hC.1 (by rw [PNode.ids_inj oldCh h.ids_nodup ho' ho hi hio]))
    exact ⟨Mirrors.frame o' hr' (fun i hi => SameContent.of_eq (hfr i hi)), y,
      by rw [hfr _ (PNode.node_mem_ids o')]; exact hy, hyp⟩
  · intro i o' hi ho' hk
    simp only [List.mem_cons, not_or]
    exact ⟨hunk i o' hi ho' hk, h.unkeyed i o' (by omega) ho' hk⟩

theorem step_create {oldCh elm n0 C byKey pos v d} (h : MPre oldCh elm n0 C byKey pos d)
    {c : PNode} {d1 : Dom} (hc : Created d c d1) (htv : c.toVNode = v) :
    Step oldCh elm C pos v d (.movable c) d1 C ∧ MPre oldCh elm n0 C byKey (pos + 1) d1 := by
  obtain ⟨x, hx, hxp⟩ := hc.detached
  refine ⟨⟨hc.ok, hc.le, hc.mirrors, hc.ids_nodup, htv, ⟨x, hx, Or.inl hxp⟩,
    Or.inr ⟨rfl, rfl, hc.frame, hc.ids_range⟩⟩, ?_⟩
  have hle := hc.le; have hn0 := h.n0_le
  refine ⟨hc.wf, h.ids_nodup, h.ids_lt, h.elm_lt, h.elm_not, by omega, h.wf_old, ?_, h.bykey,
    h.bykey_nodup, ?_⟩
  · intro o' ho' hC
    obtain ⟨hr', y, hy, hyp⟩ := h.avail o' ho' hC
    have hfr : ∀ i ∈ o'.ids, d1.nodes i = d.nodes i := fun i hi => hc.frame i
      (by have := h.ids_lt i (PNode.mem_ids_of_mem ho' hi); omega)
    exact ⟨Mirrors.frame o' hr' (fun i hi => SameContent.of_eq (hfr i hi)), y,
      by rw [hfr _ (PNode.node_mem_ids o')]; exact hy, hyp⟩
  · intro i o' hi ho' hk; exact h.unkeyed i o' (by omega) ho' hk

theorem matchOne_created (oldCh : List PNode) (byKey : String → List PNode) (pos : Nat) (v : VNode)
    (pv : PNode → Dom → PNode × Dom) (d : Dom)
    (hc : (v.key = none ∧ ∀ o, oldCh[pos]? = some o → sameVnode o v = false) ∨
      ∃ k s, v.key = some k ∧ (byKey k).span (fun o => !sameVnode o v) = (s, [])) :
    matchOne oldCh byKey pos v pv d = (.movable (createElm v d).1, byKey, (createElm v d).2) := by
  unfold matchOne
  rcases hc with ⟨hk, ho⟩ | ⟨k, s, hk, hs⟩
  · simp only [hk]
    cases hp : oldCh[pos]? with
    | none => rfl
    | some o => simp only [ho o hp, Bool.false_eq_true, ite_false]
  · simp only [hk, hs]

theorem matchOne_spec (oldCh : List PNode) (elm n0 : NodeId) (C : List NodeId)
    (byKey : String → List PNode) (pos : Nat) (v : VNode) (pv : PNode → Dom → PNode × Dom) (d : Dom)
    (h : MPre oldCh elm n0 C byKey pos d) (hv : v.WF)
    (hpv : ∀ o ∈ oldCh, o.node ∉ C → sameVnode o v = true →
      Patched d o (pv o d).1 (pv o d).2 ∧ (pv o d).1.toVNode = v) :
    ∃ C', Step oldCh elm C pos v d (matchOne oldCh byKey pos v pv d).1
        (matchOne oldCh byKey pos v pv d).2.2 C' ∧
      MPre oldCh elm n0 C' (matchOne oldCh byKey pos v pv d).2.1 (pos + 1)
        (matchOne oldCh byKey pos v pv d).2.2 := by
  have created : ∀ (hc : (v.key = none ∧ ∀ o, oldCh[pos]? = some o → sameVnode o v = false) ∨
      ∃ k s, v.key = some k ∧ (byKey k).span (fun o => !sameVnode o v) = (s, [])),
      ∃ C', Step oldCh elm C pos v d (matchOne oldCh byKey pos v pv d).1
        (matchOne oldCh byKey pos v pv d).2.2 C' ∧
      MPre oldCh elm n0 C' (matchOne oldCh byKey pos v pv d).2.1 (pos + 1)
        (matchOne oldCh byKey pos v pv d).2.2 := by
    intro hc
    rw [matchOne_created oldCh byKey pos v pv d hc]
    obtain ⟨cc, ctv⟩ := createElm_spec v d h.wf hv
    exact ⟨C, step_create h cc ctv⟩
  have hO := PNode.roots_nodup oldCh h.ids_nodup
  cases hk : v.key with
  | none =>
    cases hp : oldCh[pos]? with
    | none => exact created (Or.inl ⟨hk, fun o ho => by rw [hp] at ho; cases ho⟩)
    | some o =>
      cases hs : sameVnode o v with
      | false => exact created (Or.inl ⟨hk, fun o' ho' => by rw [hp] at ho'; cases ho'; exact hs⟩)
      | true =>
        have ho : o ∈ oldCh := List.mem_of_getElem? hp
        have hoC : o.node ∉ C := h.unkeyed pos o (Nat.le_refl _) hp (by rw [sameVnode_key o v hs, hk])
        have hokey : o.key = none := by rw [sameVnode_key o v hs, hk]
        obtain ⟨hP, htv⟩ := hpv o ho hoC hs
        have he : matchOne oldCh byKey pos v pv d = (.anchored (pv o d).1, byKey, (pv o d).2) := by
          unfold matchOne; simp only [hk, hp, hs, ite_true]
        rw [he]
        refine ⟨_, step_claim h (.anchored (pv o d).1) ho hoC hP htv rfl (fun _ => hp) ?_
          h.bykey_nodup ?_⟩
        · intro k o' ho'
          obtain ⟨h1, h2, h3⟩ := h.bykey k o' ho'
          refine ⟨h1, h2, ?_⟩
          simp only [List.mem_cons, not_or]
          refine ⟨fun e => ?_, h3⟩
          rw [PNode.node_inj h.ids_nodup h1 ho e, hokey] at h2; cases h2
        · intro i o' hi ho' _ e
          have hi1 : (oldCh.map PNode.node)[i]? = some o.node := by simp [List.getElem?_map, ho', e]
          have hi2 : (oldCh.map PNode.node)[pos]? = some o.node := by simp [List.getElem?_map, hp]
          have := idx_inj _ i pos _ hO hi1 hi2; omega
  | some k =>
    rcases hsp : (byKey k).span (fun o => !sameVnode o v) with ⟨s, _ | ⟨o, rest⟩⟩
    · exact created (Or.inr ⟨k, s, hk, hsp⟩)
    · obtain ⟨hsplit, hso⟩ := span_cons _ _ _ _ _ hsp
      have hs : sameVnode o v = true := by simpa using hso
      have hob : o ∈ byKey k := by rw [hsplit]; simp
      obtain ⟨ho, hokey, hoC⟩ := h.bykey k o hob
      obtain ⟨hP, htv⟩ := hpv o ho hoC hs
      have he : matchOne oldCh byKey pos v pv d =
          (.movable (pv o d).1, fun j => if j = k then s ++ rest else byKey j, (pv o d).2) := by
        unfold matchOne; simp only [hk, hsp]
      rw [he]
      have hnk := h.bykey_nodup k
      rw [hsplit, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnk
      refine ⟨_, step_claim h (.movable (pv o d).1) ho hoC hP htv rfl
        (fun e => absurd e (by simp [Placement.toPair])) ?_ ?_ ?_⟩
      · intro j o' ho'
        by_cases hj : j = k
        · subst hj
          simp only [ite_true] at ho'
          have hob' : o' ∈ byKey j := by
            rw [hsplit]; rcases List.mem_append.1 ho' with h' | h' <;> simp [h']
          obtain ⟨h1, h2, h3⟩ := h.bykey j o' hob'
          refine ⟨h1, h2, ?_⟩
          simp only [List.mem_cons, not_or]
          refine ⟨fun e => ?_, h3⟩
          rcases List.mem_append.1 ho' with ho' | ho'
          · exact hnk.2.2 _ (List.mem_map_of_mem ho') _ List.mem_cons_self e
          · exact hnk.2.1.1 (e ▸ List.mem_map_of_mem ho')
        · simp only [hj, ite_false] at ho'
          obtain ⟨h1, h2, h3⟩ := h.bykey j o' ho'
          refine ⟨h1, h2, ?_⟩
          simp only [List.mem_cons, not_or]
          refine ⟨fun e => hj ?_, h3⟩
          rw [PNode.node_inj h.ids_nodup h1 ho e, hokey] at h2
          cases h2; rfl
      · intro j
        by_cases hj : j = k
        · subst hj; simp only [ite_true]
          rw [List.map_append, List.nodup_append]
          exact ⟨hnk.1, hnk.2.1.2, fun a ha b hb => hnk.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
        · simp only [hj, ite_false]; exact h.bykey_nodup j
      · intro i o' _ ho' hk' e
        have := PNode.node_inj h.ids_nodup (List.mem_of_getElem? ho') ho e
        rw [this, hokey] at hk'; cases hk'

theorem mpost_nil {oldCh elm C pos d} (hw : HeapWF d) : MPost oldCh elm C pos [] d [] d :=
  ⟨hw, rfl, Nat.le_refl _, fun _ _ _ => rfl, trivial, rfl, by simp [PNode.idsList],
    by simp [PNode.idsList], by simp, by simp, by simp, by simp⟩

theorem mpost_cons {oldCh elm n0 C byKey pos v vs d pl d1 C' pls d2}
    (h : MPre oldCh elm n0 C byKey pos d) (hs : Step oldCh elm C pos v d pl d1 C')
    (hr : MPost oldCh elm C' (pos + 1) vs d1 pls d2) :
    MPost oldCh elm C pos (v :: vs) d (pl :: pls) d2 := by
  have hlt := h.ids_lt; have hn0 := h.n0_le; have le1 := hs.le; have le2 := hr.le
  have nc : ∀ N i, n0 ≤ i → ¬ InClaimed oldCh N i := fun N i hi ⟨o, ho, _, hio⟩ => by
    have := hlt i (PNode.mem_ids_of_mem ho hio); omega
  have hfree : ∀ i ∈ pl.child.ids, i < d1.next ∧ ¬ InClaimed oldCh (pls.map (·.child.node)) i := by
    intro i hi
    rcases hs.kind with ⟨o, ho, _, hC', _, _, hrg, _⟩ | ⟨_, _, _, hrg⟩
    · rcases hrg i hi with hio | hio
      · have hi0 := hlt i (PNode.mem_ids_of_mem ho hio)
        refine ⟨by omega, fun ⟨o', ho', hN, hio'⟩ => ?_⟩
        have e := PNode.ids_inj oldCh h.ids_nodup ho' ho hio' hio
        rw [e] at hN
        obtain ⟨pl', hpl', hpe⟩ := List.mem_map.1 hN
        rcases hr.roots pl' hpl' with ⟨o'', _, hoC'', he''⟩ | ⟨hf, _⟩
        · apply hoC''; rw [hC', ← he'', hpe]; exact List.mem_cons_self
        · have := hlt _ (PNode.mem_ids_of_mem ho (PNode.node_mem_ids o)); rw [hpe] at hf; omega
      · exact ⟨hio.2, nc _ i (by omega)⟩
    · have := hrg i hi; exact ⟨this.2, nc _ i (by omega)⟩
  refine ⟨hr.wf, by rw [hr.ok, hs.ok], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hnc
    have hnc' : ¬ InClaimed oldCh (pls.map (·.child.node)) i := fun hc => hnc (hc.cons _)
    rw [hr.frame i (by omega) hnc']
    rcases hs.kind with ⟨o, ho, _, _, hnode, hfr, _, _⟩ | ⟨_, _, hfr, _⟩
    · exact hfr i hi (fun hio => hnc ⟨o, ho, by simp [hnode], hio⟩)
    · exact hfr i hi
  · exact ⟨Mirrors.frame _ hs.mirrors (fun i hi => SameContent.of_eq (hr.frame i (hfree i hi).1 (hfree i hi).2)),
      hr.mirrors⟩
  · simp only [List.map_cons, PNode.toVNodes, hs.toV, hr.toV]
  · simp only [List.map_cons]
    rw [PNode.idsList_cons, List.nodup_append]
    refine ⟨hs.ids_nodup, hr.ids_nodup, fun a ha b hb e => ?_⟩
    subst e
    rcases hr.ids_range a hb with hc | hc
    · exact (hfree a ha).2 hc
    · have := (hfree a ha).1; omega
  · intro i hi
    simp only [List.map_cons] at hi
    rw [PNode.idsList_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · rcases hs.kind with ⟨o, ho, _, _, hnode, _, hrg, _⟩ | ⟨_, _, _, hrg⟩
      · rcases hrg i hi with hio | hio
        · exact Or.inl ⟨o, ho, by simp [hnode], hio⟩
        · exact Or.inr ⟨hio.1, by omega⟩
      · have := hrg i hi; exact Or.inr ⟨this.1, by omega⟩
    · rcases hr.ids_range i hi with hc | hc
      · exact Or.inl (hc.cons _)
      · exact Or.inr ⟨by omega, hc.2⟩
  · intro pl' hpl'
    rcases List.mem_cons.1 hpl' with rfl | hpl'
    · rcases hs.kind with ⟨o, ho, hoC, _, hnode, _⟩ | ⟨_, _, _, hrg⟩
      · exact Or.inl ⟨o, ho, hoC, hnode⟩
      · have := hrg _ (PNode.node_mem_ids _); exact Or.inr ⟨this.1, by omega⟩
    · rcases hr.roots pl' hpl' with ⟨o, ho, hoC, hnode⟩ | hf
      · refine Or.inl ⟨o, ho, fun hc => hoC ?_, hnode⟩
        rcases hs.kind with ⟨_, _, _, hC', _⟩ | ⟨hC', _⟩
        · rw [hC']; exact List.mem_cons_of_mem _ hc
        · rw [hC']; exact hc
      · exact Or.inr ⟨by omega, hf.2⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hr.roots_nodup⟩
    obtain ⟨pl', hpl', hpe⟩ := List.mem_map.1 hm
    rcases hs.kind with ⟨o, ho, _, _, hnode, _⟩ | ⟨_, _, _, hrg⟩
    · exact (hfree _ (PNode.node_mem_ids _)).2 ⟨o, ho,
        List.mem_map.2 ⟨pl', hpl', by rw [hpe, hnode]⟩, by rw [hnode]; exact PNode.node_mem_ids _⟩
    · have hp := hrg _ (PNode.node_mem_ids _)
      rcases hr.roots pl' hpl' with ⟨o, ho, _, hnode⟩ | hf
      · have := hlt _ (PNode.mem_ids_of_mem ho (PNode.node_mem_ids o))
        rw [← hnode, hpe] at this; omega
      · rw [hpe] at hf; omega
  · intro i c hi
    cases i with
    | zero =>
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
      rcases hs.kind with ⟨o, _, _, _, hnode, _, _, ha⟩ | ⟨_, hf, _⟩
      · have e1 := ha (by rw [hi])
        have e2 : c = o.node := by rw [← hnode, ← Placement.toPair_snd pl, hi]
        rw [List.getElem?_map, Nat.add_zero, e1, e2]; rfl
      · rw [hi] at hf; cases hf
    | succ i =>
      simp only [List.map_cons, List.getElem?_cons_succ] at hi
      have := hr.anchored_at i c hi
      rwa [show pos + 1 + i = pos + (i + 1) by omega] at this
  · intro pl' hpl'
    rcases List.mem_cons.1 hpl' with rfl | hpl'
    · obtain ⟨x, hx, hxp⟩ := hs.parent
      have hf := hfree _ (PNode.node_mem_ids _)
      exact ⟨x, by rw [hr.frame _ hf.1 hf.2]; exact hx, hxp⟩
    · exact hr.parent pl' hpl'

theorem oldIndexOf_nonneg {oldCh : List PNode} {pl : Placement} (h : 0 ≤ oldIndexOf oldCh pl) :
    ∃ j, ∃ hj : j < oldCh.length, oldIndexOf oldCh pl = j ∧ oldCh[j].node = pl.child.node := by
  unfold oldIndexOf at *
  cases hf : oldCh.findIdx? (fun o => decide (o.node = pl.child.node)) with
  | none => rw [hf] at h; simp at h
  | some j =>
    obtain ⟨hj, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    exact ⟨j, hj, rfl, by simpa using hp⟩

theorem matchedPrefix_spec : ∀ (l : List Int) (k : Nat),
    matchedPrefix l k ≤ l.length ∧ ∀ j, j < matchedPrefix l k → l[j]? = some ((k + j : Nat) : Int)
  | [], _ => by simp [matchedPrefix]
  | i :: is, k => by
    simp only [matchedPrefix]
    split
    · rename_i hi
      obtain ⟨h1, h2⟩ := matchedPrefix_spec is (k + 1)
      refine ⟨by simp; omega, fun j hj => ?_⟩
      cases j with
      | zero => simp [hi]
      | succ j =>
        rw [List.getElem?_cons_succ, h2 j (by omega)]
        congr 2; omega
    · simp

/-- Removing the old children that were not reused, from a child list `L'`
that holds the reused ones in order, leaves exactly those. -/
theorem remove_unused {oldCh : List PNode} {elm : NodeId} {R L' : List NodeId} {d : Dom} {ex : DomNode}
    (hw : HeapWF d) (he : d.nodes elm = some { ex with children := L' })
    (hO : (oldCh.map PNode.node).Nodup) (helm : ∀ o ∈ oldCh, o.node ≠ elm)
    (hkeep : keepIn R L' = R) (hsub : ∀ x ∈ L', x ∈ oldCh.map PNode.node ∨ x ∈ R)
    (hsup : ∀ x ∈ oldCh.map PNode.node, x ∉ R → x ∈ L') :
    HeapWF (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d) ∧
    (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d).ok = d.ok ∧
    (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d).next = d.next ∧
    (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d).nodes elm =
      some { ex with children := R } ∧
    (∀ m, m ≠ elm → SameContent d (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d) m) ∧
    (∀ m, m ≠ elm → m ∉ oldCh.map PNode.node →
      (removeAllVnodes elm (oldCh.filter (fun o => decide (o.node ∉ R))) d).nodes m = d.nodes m) := by
  have hU : ∀ u ∈ oldCh.filter (fun o => decide (o.node ∉ R)),
      u.node ∈ { ex with children := L' }.children ∧ u.node ≠ elm := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := List.mem_filter.1 hu
    simp only [decide_eq_true_eq] at hu2
    exact ⟨hsup _ (List.mem_map_of_mem hu1) hu2, helm u hu1⟩
  have hUnd : ((oldCh.filter (fun o => decide (o.node ∉ R))).map PNode.node).Nodup :=
    List.Nodup.sublist (List.filter_sublist.map PNode.node) hO
  obtain ⟨w4, ok4, nx4, ne4, sc4, fr4⟩ := removeAll_spec elm _ d _ hw he hUnd hU
  have hfilt : L'.filter (fun x => decide (x ∉ (oldCh.filter (fun o => decide (o.node ∉ R))).map PNode.node)) = R := by
    refine Eq.trans ?_ hkeep
    unfold keepIn
    apply List.filter_congr
    intro x hx
    by_cases hxR : x ∈ R
    · have : x ∉ (oldCh.filter (fun o => decide (o.node ∉ R))).map PNode.node := by
        intro hm; obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
        exact (by simpa using (List.mem_filter.1 hu).2 : u.node ∉ R) hxR
      rw [decide_eq_true this, decide_eq_true hxR]
    · have hxO : x ∈ oldCh.map PNode.node := by
        rcases hsub x hx with h1 | h1
        · exact h1
        · exact absurd h1 hxR
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hxO
      have : o.node ∈ (oldCh.filter (fun o => decide (o.node ∉ R))).map PNode.node :=
        List.mem_map_of_mem (List.mem_filter.2 ⟨ho, by simpa using hxR⟩)
      rw [decide_eq_false (fun hn => hn this), decide_eq_false hxR]
  refine ⟨w4, ok4, nx4, by rw [ne4, hfilt], sc4, fun m hm hmO => fr4 m hm (fun h => hmO ?_)⟩
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
  exact List.mem_map_of_mem (List.mem_filter.1 hu).1

theorem finish_spec {oldCh : List PNode} {elm : NodeId} {byKey : String → List PNode} {vs : List VNode}
    {pls : List Placement} {d1 d2 : Dom} {ex1 : DomNode}
    (h : MPre oldCh elm d1.next [] byKey 0 d1) (hp : MPost oldCh elm [] 0 vs d1 pls d2)
    (he1 : d1.nodes elm = some ex1) (hch : ex1.children = oldCh.map PNode.node) :
    HeapWF (finishChildren elm oldCh pls d2).2 ∧ (finishChildren elm oldCh pls d2).2.ok = d1.ok ∧
    (finishChildren elm oldCh pls d2).2.next = d2.next ∧
    (finishChildren elm oldCh pls d2).1 = pls.map (·.child) ∧
    (finishChildren elm oldCh pls d2).2.nodes elm = some { ex1 with children := pls.map (·.child.node) } ∧
    (∀ i, i < d1.next → i ∉ PNode.idsList oldCh → i ≠ elm →
      (finishChildren elm oldCh pls d2).2.nodes i = d1.nodes i) ∧
    MirrorsList (finishChildren elm oldCh pls d2).2 (pls.map (·.child)) := by
  have hel := h.elm_lt; have helm := h.elm_not
  have nc : ∀ N i, i ∉ PNode.idsList oldCh → ¬ InClaimed oldCh N i := fun _ _ hi hc => hi hc.mem
  have he2 : d2.nodes elm = some ex1 := by rw [hp.frame elm hel (nc _ _ helm)]; exact he1
  have hroot : ∀ pl ∈ pls, pl.child.node ∈ PNode.idsList oldCh ∨ d1.next ≤ pl.child.node := by
    intro pl hpl
    rcases hp.roots pl hpl with ⟨o, ho, _, he⟩ | hf
    · exact Or.inl (he ▸ PNode.mem_ids_of_mem ho (PNode.node_mem_ids o))
    · exact Or.inr hf.1
  have hpls : ∀ pl ∈ pls, pl.child.node ≠ elm ∧ ∃ x, d2.nodes pl.child.node = some x ∧
      (x.parent = none ∨ x.parent = some elm) := by
    intro pl hpl
    refine ⟨fun e => ?_, hp.parent pl hpl⟩
    rcases hroot pl hpl with h1 | h1
    · exact helm (e ▸ h1)
    · omega
  have hO := PNode.roots_nodup oldCh h.ids_nodup
  have helmO : ∀ o ∈ oldCh, o.node ≠ elm := fun o ho e =>
    helm (e ▸ PNode.mem_ids_of_mem ho (PNode.node_mem_ids o))
  have hRP : (pls.map Placement.toPair).map (·.2) = pls.map (·.child.node) := toPairs_snd pls
  have key : ∃ d3, finishChildren elm oldCh pls d2 = (pls.map (·.child), d3) ∧ HeapWF d3 ∧
      d3.ok = d2.ok ∧ d3.next = d2.next ∧
      d3.nodes elm = some { ex1 with children := pls.map (·.child.node) } ∧
      (∀ m, m ≠ elm → SameContent d2 d3 m) ∧
      (∀ m, m ≠ elm → m ∉ pls.map (·.child.node) → m ∉ oldCh.map PNode.node → d3.nodes m = d2.nodes m) := by
    unfold finishChildren
    dsimp only
    split
    · -- every old child was reused at its own position: the rest are appended
      rename_i hstart
      refine ⟨_, rfl, ?_⟩
      rw [hstart]
      obtain ⟨hlen, hidx⟩ := matchedPrefix_spec (pls.map (oldIndexOf oldCh)) 0
      rw [hstart, List.length_map] at hlen
      rw [hstart] at hidx
      have htake : (pls.take oldCh.length).map (·.child.node) = oldCh.map PNode.node := by
        apply List.ext_getElem (by simp; omega)
        intro j h1 h2
        simp only [List.getElem_map, List.getElem_take]
        have hj := hidx j (by simpa using h2)
        rw [List.getElem?_map, List.getElem?_eq_getElem (by simp at h1; omega)] at hj
        simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hj
        obtain ⟨j', hj', e, hn⟩ := oldIndexOf_nonneg (by rw [hj]; omega)
        rw [hj] at e
        have : j' = j := by omega
        subst this; exact hn.symm
      have hR : pls.map (·.child.node) =
          oldCh.map PNode.node ++ (pls.drop oldCh.length).map (·.child.node) := by
        rw [← htake, ← List.map_append, List.take_append_drop]
      have hRnd := hp.roots_nodup
      rw [hR, List.nodup_append] at hRnd
      have hdrop : ∀ c ∈ (pls.map (·.child)).drop oldCh.length, c.node ≠ elm ∧
          ∃ cx, d2.nodes c.node = some cx ∧ cx.parent = none := by
        intro c hc
        rw [← List.map_drop] at hc
        obtain ⟨pl, hpl, rfl⟩ := List.mem_map.1 hc
        obtain ⟨hne, x, hx, hxp⟩ := hpls pl (List.mem_of_mem_drop hpl)
        refine ⟨hne, x, hx, ?_⟩
        rcases hxp with hxp | hxp
        · exact hxp
        · obtain ⟨px, hpx, hm⟩ := hp.wf.parent_child _ x elm hx hxp
          rw [he2] at hpx; cases hpx
          rw [hch] at hm
          exact absurd rfl (hRnd.2.2 _ hm _ (List.mem_map_of_mem hpl))
      have hcs : ((pls.map (·.child)).drop oldCh.length).map PNode.node =
          (pls.drop oldCh.length).map (·.child.node) := by
        rw [← List.map_drop, List.map_map]; rfl
      obtain ⟨w3, ok3, nx3, nd3⟩ := appendAll_spec elm ((pls.map (·.child)).drop oldCh.length) d2 ex1
        hp.wf he2 (by rw [hcs]; exact hRnd.2.1) hdrop
      rw [hcs] at nd3
      refine ⟨w3, ok3, nx3, by rw [nd3, ite_eq_left rfl, hch, ← hR], ?_, ?_⟩
      · intro m hm
        unfold SameContent
        rw [nd3, ite_eq_right hm]
        split
        · cases d2.nodes m <;> rfl
        · rfl
      · intro m hm hmR _
        rw [nd3, ite_eq_right hm, ite_eq_right (fun h => hmR (by rw [hR]; exact List.mem_append_right _ h))]
    · split
      · -- an anchored child after the prefix: the general placement loop
        have hcur : oldCh.head?.map PNode.node = none ∨
            ∃ o, oldCh.head?.map PNode.node = some o ∧ o ∈ ex1.children := by
          cases oldCh with
          | nil => exact Or.inl rfl
          | cons o os => exact Or.inr ⟨o.node, rfl, by rw [hch]; exact List.mem_cons_self⟩
        obtain ⟨w3, ok3, nx3, ne3, sc3, fr3⟩ :=
          place_spec elm (pls.map (·.child.node)) pls _ d2 ex1 hp.wf he2 hcur hp.roots_nodup hpls
        rw [hch] at ne3
        have hcorr := placeList_correct (oldCh.map PNode.node) (pls.map Placement.toPair) hO
          (by rw [hRP]; exact hp.roots_nodup)
          (fun i c hi => by have := hp.anchored_at i c hi; rwa [Nat.zero_add] at this)
        rw [hRP, List.head?_map] at hcorr
        obtain ⟨w4, ok4, nx4, ne4, sc4, fr4⟩ := remove_unused w3 ne3 hO helmO hcorr.1
          (fun x hx => by
            rcases placeList_sub _ _ _ _ x hx with h1 | h1
            · exact Or.inl h1
            · rw [hRP] at h1; exact Or.inr h1)
          (fun x hx hxR => placeList_keep _ _ _ _ x hx (by rw [hRP]; exact hxR))
        exact ⟨_, rfl, w4, by rw [ok4, ok3], by rw [nx4, nx3], ne4,
          fun m hm => (sc3 m hm).trans (sc4 m hm), fun m hm hmR hmO => by rw [fr4 m hm hmO, fr3 m hm hmR]⟩
      · -- no anchored child after the prefix: keep the longest increasing run
        have hidx : ∀ i (hi : i < (pls.map (·.child.node)).length),
            0 ≤ (pls.map (oldIndexOf oldCh)).getD i (-1) →
            ∃ j, ∃ hj : j < ex1.children.length, (pls.map (oldIndexOf oldCh)).getD i (-1) = j ∧
              ex1.children[j] = (pls.map (·.child.node))[i] := by
          intro i hi h0
          rw [List.length_map] at hi
          have hg : (pls.map (oldIndexOf oldCh)).getD i (-1) = oldIndexOf oldCh pls[i] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
          rw [hg] at h0 ⊢
          obtain ⟨j, hj, e, hn⟩ := oldIndexOf_nonneg h0
          have hj' : j < ex1.children.length := by rw [hch, List.length_map]; exact hj
          refine ⟨j, hj', e, ?_⟩
          simp only [hch, List.getElem_map, hn]
        obtain ⟨w3, ok3, nx3, L', ne3, hk3, hs3, hu3, sc3, fr3⟩ :=
          placeWithFewestMoves_spec elm (pls.map (·.child.node)) (pls.map (oldIndexOf oldCh)) d2 ex1
            hp.wf he2 (by rw [hch]; exact hO) hp.roots_nodup
            (fun x hx => by obtain ⟨pl, hpl, rfl⟩ := List.mem_map.1 hx; exact hpls pl hpl) hidx
        obtain ⟨w4, ok4, nx4, ne4, sc4, fr4⟩ := remove_unused w3 ne3 hO helmO hk3
          (fun x hx => by rw [← hch]; exact hs3 x hx)
          (fun x hx _ => hu3 x (by rw [hch]; exact hx))
        exact ⟨_, rfl, w4, by rw [ok4, ok3], by rw [nx4, nx3], ne4,
          fun m hm => (sc3 m hm).trans (sc4 m hm), fun m hm hmR hmO => by rw [fr4 m hm hmO, fr3 m hm hmR]⟩
  obtain ⟨d3, hfc, w3, ok3, nx3, ne3, sc3, fr3⟩ := key
  rw [hfc]
  have hne : ∀ i ∈ PNode.idsList (pls.map (·.child)), i ≠ elm := by
    intro i hi e; subst e
    rcases hp.ids_range _ hi with hc | hc
    · exact helm hc.mem
    · omega
  refine ⟨w3, by rw [ok3, hp.ok], nx3, rfl, ne3, ?_, ?_⟩
  · intro i hi hio hie
    have hiO : i ∉ oldCh.map PNode.node := by
      intro hm; obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
      exact hio (PNode.mem_ids_of_mem hu (PNode.node_mem_ids u))
    have hiR : i ∉ pls.map (·.child.node) := by
      intro hm; obtain ⟨pl, hpl, rfl⟩ := List.mem_map.1 hm
      rcases hroot pl hpl with h1 | h1
      · exact hio h1
      · omega
    rw [fr3 i hie hiR hiO, hp.frame i hi (nc _ _ hio)]
  · exact MirrorsList.frame _ hp.mirrors (fun i hi => sc3 i (hne i hi))

end Snabbdom
