import Snabbdom.Proofs.PatchVnode

namespace Snabbdom

/-- The ids of `o` below its root. -/
def PNode.sub : PNode → List NodeId
  | .elem _ _ ch _ => PNode.idsList ch
  | _ => []

theorem PNode.ids_eq (o : PNode) : o.ids = o.node :: o.sub := by
  cases o <;> simp [PNode.ids, PNode.sub, PNode.node]

mutual
theorem Mirrors.children_sub : ∀ (o : PNode) {d : Dom}, Mirrors d o → ∀ q ∈ o.ids, ∀ qx, d.nodes q = some qx →
    ∀ c ∈ qx.children, c ∈ o.sub
  | .text s n, d, h, q, hq, qx, hqx, c, hc => by
    obtain ⟨x, hx, _, hch⟩ := h
    simp only [PNode.ids, List.mem_singleton] at hq; subst hq
    rw [hx] at hqx; cases hqx; rw [hch] at hc; cases hc
  | .comment s n, d, h, q, hq, qx, hqx, c, hc => by
    obtain ⟨x, hx, _, hch⟩ := h
    simp only [PNode.ids, List.mem_singleton] at hq; subst hq
    rw [hx] at hqx; cases hqx; rw [hch] at hc; cases hc
  | .elem sel data ch n, d, h, q, hq, qx, hqx, c, hc => by
    obtain ⟨x, hx, _, _, hch, hl⟩ := h
    simp only [PNode.sub]
    rw [PNode.ids_elem, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rw [hx] at hqx; cases hqx; rw [hch] at hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact PNode.mem_ids_of_mem hc' (PNode.node_mem_ids c')
    · exact MirrorsList.children_sub ch hl q hq qx hqx c hc
theorem MirrorsList.children_sub : ∀ (L : List PNode) {d : Dom}, MirrorsList d L →
    ∀ q ∈ PNode.idsList L, ∀ qx, d.nodes q = some qx → ∀ c ∈ qx.children, c ∈ PNode.idsList L
  | [], _, _, q, hq, _, _, _, _ => by simp [PNode.idsList] at hq
  | p :: ps, d, h, q, hq, qx, hqx, c, hc => by
    rw [PNode.idsList_cons, List.mem_append] at hq ⊢
    rcases hq with hq | hq
    · left; rw [PNode.ids_eq]; exact List.mem_cons_of_mem _ (Mirrors.children_sub p h.1 q hq qx hqx c hc)
    · right; exact MirrorsList.children_sub ps h.2 q hq qx hqx c hc
end

theorem parent_not_mem {d : Dom} {old : PNode} (hw : HeapWF d) (hr : Mirrors d old) (hn : old.ids.Nodup)
    {x : DomNode} (hx : d.nodes old.node = some x) {p : NodeId} (hp : x.parent = some p) :
    p ∉ old.ids := by
  intro hm
  obtain ⟨px, hpx, hc⟩ := hw.parent_child _ _ _ hx hp
  have := Mirrors.children_sub old hr p hm px hpx _ hc
  rw [PNode.ids_eq, List.nodup_cons] at hn
  exact hn.1 this

theorem Mirrors.node_exists {d : Dom} {o : PNode} (h : Mirrors d o) : ∃ x, d.nodes o.node = some x := by
  cases o with
  | text s n => obtain ⟨x, hx, _⟩ := h; exact ⟨x, hx⟩
  | comment s n => obtain ⟨x, hx, _⟩ := h; exact ⟨x, hx⟩
  | elem sel data ch n => obtain ⟨x, hx, _⟩ := h; exact ⟨x, hx⟩

/-! ### Replacing a child in place -/

def replaceIn (a n : NodeId) (L : List NodeId) : List NodeId :=
  L.map (fun c => if c = a then n else c)

theorem replaceIn_not_mem (a n : NodeId) : ∀ (L : List NodeId), a ∉ L → replaceIn a n L = L
  | [], _ => rfl
  | y :: ys, h => by
    simp only [List.mem_cons, not_or] at h
    have hy : y ≠ a := fun e => h.1 e.symm
    show (if y = a then n else y) :: replaceIn a n ys = y :: ys
    rw [ite_eq_right hy, replaceIn_not_mem a n ys h.2]

theorem replaceIn_self (a : NodeId) : ∀ (L : List NodeId), replaceIn a a L = L
  | [] => rfl
  | y :: ys => by
    show (if y = a then a else y) :: replaceIn a a ys = y :: ys
    rw [replaceIn_self a ys]
    by_cases hy : y = a
    · rw [ite_eq_left hy, hy]
    · rw [ite_eq_right hy]

theorem filter_not_mem (a : NodeId) (L : List NodeId) (h : a ∉ L) :
    L.filter (fun x => decide (x ∉ [a])) = L :=
  List.filter_eq_self.2 (fun x hx => by
    simp only [List.mem_singleton, decide_eq_true_eq]; exact fun e => h (e ▸ hx))

theorem insert_after_replace (a n : NodeId) : ∀ (L : List NodeId), L.Nodup → a ∈ L → n ∉ L →
    (insertAt n (after a L) L).filter (fun x => decide (x ∉ [a])) = replaceIn a n L
  | [], _, h, _ => by cases h
  | y :: ys, hnd, ha, hn => by
    simp only [List.nodup_cons] at hnd
    simp only [List.mem_cons, not_or] at hn
    by_cases hy : y = a
    · subst hy
      have hna : n ≠ y := hn.1
      cases ys with
      | nil =>
        simp [after, insertAt, replaceIn, hna]
      | cons z zs =>
        simp only [List.mem_cons, not_or] at hnd
        have hzy : z ≠ y := fun e => hnd.1.1 e.symm
        simp only [after, ite_true, List.head?_cons, insertAt, hzy.symm, ite_false]
        rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp [hna]),
          filter_not_mem y (z :: zs) (by simp [hnd.1.1, hnd.1.2])]
        show n :: z :: zs = (if y = y then n else y) :: replaceIn y n (z :: zs)
        rw [ite_eq_left rfl, replaceIn_not_mem y n _ (by simp [hnd.1.1, hnd.1.2])]
    · have ha' : a ∈ ys := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hy
        · exact e
      simp only [after, hy, ite_false]
      have hins : insertAt n (after a ys) (y :: ys) = y :: insertAt n (after a ys) ys := by
        cases hr : after a ys with
        | none => simp [insertAt]
        | some r =>
          have hry : y ≠ r := fun e => hnd.1 (e ▸ after_mem a r ys hr)
          simp [insertAt, hry]
      rw [hins, List.filter_cons_of_pos (by simp [hy]),
        insert_after_replace a n ys hnd.2 ha' hn.2]
      show y :: replaceIn a n ys = (if y = a then n else y) :: replaceIn a n ys
      rw [ite_eq_right hy]

/-- `patch` is correct: the result is valid, describes `v`, shows `v.render`
in the DOM, sits where `old` was, and nothing else in the document changed. -/
theorem patch_correct (old : PNode) (v : VNode) (d : Dom) (h : Valid d old) (hv : v.WF) :
    Valid (patch old v d).2 (patch old v d).1 ∧ (patch old v d).1.toVNode = v ∧
    Shows (patch old v d).2 (patch old v d).1.node v.render ∧
    -- the rest of the document is untouched...
    (∀ i, i < d.next → i ∉ old.ids → d.parentNode old.node ≠ some i →
      (patch old v d).2.nodes i = d.nodes i) ∧
    -- ...except that the parent now has the new node where the old one was
    (∀ p px, d.parentNode old.node = some p → d.nodes p = some px →
      (patch old v d).2.nodes p =
        some { px with children := replaceIn old.node (patch old v d).1.node px.children }) ∧
    (d.parentNode old.node = none → ∃ x, (patch old v d).2.nodes (patch old v d).1.node = some x ∧
      x.parent = none) := by
  obtain ⟨hw, hok, hr, hnd, hbd, hwf⟩ := h
  obtain ⟨x, hx⟩ := Mirrors.node_exists hr
  have hold : old.node ∈ old.ids := PNode.node_mem_ids old
  by_cases hs : sameVnode old v = true
  · have hpe : patch old v d = patchVnode old v d := by simp [patch, hs]
    rw [hpe]
    obtain ⟨P, tv⟩ := patchVnode_spec v old d ⟨hw, hr, hnd, hbd, hwf⟩ hv hs
    generalize patchVnode old v d = r at P tv ⊢
    obtain ⟨nv, d'⟩ := r
    dsimp only at *
    have hle := P.le
    refine ⟨⟨P.wf, by rw [P.ok, hok], P.mirrors, P.ids_nodup, ?_, by rw [tv]; exact hv⟩, tv,
      by have := Mirrors.shows _ P.mirrors; rwa [tv] at this, ?_, ?_, ?_⟩
    · intro i hi
      rcases P.ids_range i hi with h1 | h1
      · have := hbd i h1; omega
      · exact h1.2
    · intro i hi hio _; exact P.frame i hi hio
    · intro p px hp hpx
      simp only [Dom.parentNode_eq, hx, Option.bind_some] at hp
      have hpo := parent_not_mem hw hr hnd hx hp
      have hplt := hw.bound p px hpx
      rw [P.frame p hplt hpo, hpx, P.node, replaceIn_self]
    · intro hp
      simp only [Dom.parentNode_eq, hx, Option.bind_some] at hp
      obtain ⟨x', hx', hxp⟩ := P.parent x hx
      exact ⟨x', by rw [P.node]; exact hx', by rw [hxp, hp]⟩
  · have hs' : sameVnode old v = false := by simpa using hs
    obtain ⟨cc, ctv⟩ := createElm_spec v d hw hv
    have hpe : patch old v d =
        match d.parentNode old.node with
        | some p => ((createElm v d).1, removeAllVnodes p [old]
            ((createElm v d).2.insertBefore p (createElm v d).1.node
              ((createElm v d).2.nextSibling old.node)))
        | none => ((createElm v d).1, (createElm v d).2) := by
      unfold patch; rw [ite_eq_right hs]; (try rfl)
    rw [hpe]
    generalize createElm v d = r at cc ctv ⊢
    obtain ⟨nv, d1⟩ := r
    dsimp only at *
    have hle1 := cc.le
    obtain ⟨nx, hnx, hnp⟩ := cc.detached
    have hnr := cc.ids_range nv.node (PNode.node_mem_ids nv)
    have valid1 : ∀ d2 : Dom, HeapWF d2 → d2.ok = d1.ok → d2.next = d1.next →
        (∀ i ∈ nv.ids, SameContent d1 d2 i) → Valid d2 nv := fun d2 w2 ok2 nx2 sc2 =>
      ⟨w2, by rw [ok2, cc.ok, hok], Mirrors.frame nv cc.mirrors sc2, cc.ids_nodup,
        fun i hi => by rw [nx2]; exact (cc.ids_range i hi).2, by rw [ctv]; exact hv⟩
    cases hpar : d.parentNode old.node with
    | none =>
      dsimp only
      refine ⟨valid1 d1 cc.wf rfl rfl (fun _ _ => SameContent.of_eq rfl), ctv,
        by have := Mirrors.shows _ cc.mirrors; rwa [ctv] at this, fun i hi _ _ => cc.frame i hi,
        fun p _ hp => (by cases hp), fun _ => ⟨nx, hnx, hnp⟩⟩
    | some p =>
      dsimp only
      have hxp : x.parent = some p := by simpa [Dom.parentNode_eq, hx] using hpar
      obtain ⟨px, hpx, hmem⟩ := hw.parent_child _ _ _ hx hxp
      have hplt := hw.bound p px hpx
      have hpo := parent_not_mem hw hr hnd hx hxp
      have hop : old.node ≠ p := fun e => hpo (e ▸ hold)
      have hpx1 : d1.nodes p = some px := by rw [cc.frame p hplt]; exact hpx
      have hx1 : d1.nodes old.node = some x := by rw [cc.frame _ (hbd _ hold)]; exact hx
      have hns := Dom.nextSibling_eq cc.wf hpx1 hx1 (Or.inr hxp)
      have hchl : ∀ c ∈ px.children, c < d.next := fun c hc => by
        obtain ⟨y, hy, _⟩ := hw.child_parent p px c hpx hc
        exact hw.bound c y hy
      have hnvp : nv.node ≠ p := by omega
      have hnvc : nv.node ∉ px.children := fun hm => by have := hchl _ hm; omega
      have hi : Dom.InsertOk (d1.log (.insertBefore p nv.node (d1.nextSibling old.node))) p nv.node
          (d1.nextSibling old.node) px nx := by
        refine ⟨hpx1, hnx, hnvp, Or.inl hnp, fun r hr' => ?_⟩
        rw [hns] at hr'
        have hrm := after_mem _ _ _ hr'
        exact ⟨hrm, fun e => hnvc (e ▸ hrm)⟩
      have hwl := Dom.log_wf (.insertBefore p nv.node (d1.nextSibling old.node)) cc.wf
      have hN := Dom.preInsert_nodes hwl hi
      generalize hd2 : d1.insertBefore p nv.node (d1.nextSibling old.node) = d2
      have hd2' : d2 = (d1.log (.insertBefore p nv.node (d1.nextSibling old.node))).preInsert p nv.node
          (d1.nextSibling old.node) := hd2.symm
      have w2 : HeapWF d2 := hd2' ▸ Dom.preInsert_wf hwl hi
      have hpx2 : d2.nodes p =
          some { px with children := (insertAt nv.node (after old.node px.children) px.children) } := by
        rw [hd2', hN, hns]; simp [List.erase_of_not_mem hnvc]
      obtain ⟨w3, ok3, nx3, ne3, sc3, fr3⟩ := removeAll_spec p [old] d2 _ w2 hpx2 (by simp)
        (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho
          exact ⟨by rw [mem_insertAt]; exact Or.inr hmem, hop⟩)
      have sc12 : ∀ i, i ≠ p → SameContent d1 d2 i := by
        intro i hip
        unfold SameContent; rw [hd2', hN, ite_eq_right hip]
        split
        · rename_i e; subst e; simp [hnx, DomNode.content]
        · rfl
      have hnvi : ∀ i ∈ nv.ids, i ≠ p := fun i hi e => by
        have := (cc.ids_range i hi).1; omega
      have nx2 : d2.next = d1.next := by rw [hd2']; simp
      refine ⟨valid1 _ w3 (by rw [ok3, hd2', Dom.preInsert_ok hi]; rfl) (by rw [nx3, nx2])
          (fun i hi => (sc12 i (hnvi i hi)).trans (sc3 i (hnvi i hi))), ctv, ?_, ?_, ?_, ?_⟩
      · have := Mirrors.shows _ (Mirrors.frame nv cc.mirrors
          (fun i hi => (sc12 i (hnvi i hi)).trans (sc3 i (hnvi i hi))))
        rwa [ctv] at this
      · intro i hi hio hip
        have hip' : i ≠ p := fun e => hip (by rw [e])
        have hio' : i ≠ old.node := fun e => hio (e ▸ hold)
        have hinv : i ≠ nv.node := by omega
        rw [fr3 i hip' (by simp [hio']), hd2', hN, ite_eq_right hip', ite_eq_right hinv, Dom.nodes_log, cc.frame i hi]
      · intro p' px' hp' hpx'
        cases hp'
        rw [hpx] at hpx'; cases hpx'
        rw [ne3]
        dsimp only
        rw [List.map_singleton, insert_after_replace _ _ _ (hw.nodup p px hpx) hmem hnvc]
      · intro hp'; exact (by cases hp')

/-! ### Diff ≡ recreate -/

mutual
theorem Shows.unique : ∀ (t : DTree) {d : Dom} {n : NodeId} {t' : DTree}, Shows d n t → Shows d n t' → t = t'
  | .text s, d, n, t', h, h' => by
    obtain ⟨x, hx, hk, _⟩ := h
    cases t' with
    | text s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'; rfl
    | comment s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
    | elem sel a ts => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
  | .comment s, d, n, t', h, h' => by
    obtain ⟨x, hx, hk, _⟩ := h
    cases t' with
    | text s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
    | comment s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'; rfl
    | elem sel a ts => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
  | .elem sel a ts, d, n, t', h, h' => by
    obtain ⟨x, hx, hk, ha, hl⟩ := h
    cases t' with
    | text s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
    | comment s' => obtain ⟨x', hx', hk', _⟩ := h'; rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
    | elem sel' a' ts' =>
      obtain ⟨x', hx', hk', ha', hl'⟩ := h'
      rw [hx] at hx'; cases hx'; rw [hk] at hk'; cases hk'
      rw [ha] at ha'; subst ha'
      rw [ShowsList.unique ts hl hl']
theorem ShowsList.unique : ∀ (ts : List DTree) {d : Dom} {ns : List NodeId} {ts' : List DTree},
    ShowsList d ns ts → ShowsList d ns ts' → ts = ts'
  | [], d, ns, ts', h, h' => by
    match ns, ts', h, h' with
    | [], [], _, _ => rfl
    | _ :: _, _, h, _ => exact h.elim
    | [], _ :: _, _, h' => exact h'.elim
  | t :: ts, d, ns, ts', h, h' => by
    match ns, ts', h, h' with
    | [], _, h, _ => exact h.elim
    | _ :: _, [], _, h' => exact h'.elim
    | n :: ns, t' :: ts', h, h' => rw [Shows.unique t h.1 h'.1, ShowsList.unique ts h.2 h'.2]
end

/-- **Diff ≡ recreate.** Whatever DOM tree you read at the patched node is
exactly the tree you would read after rendering `v` from scratch, in any
well-formed DOM. -/
theorem diff_eq_recreate (old : PNode) (v : VNode) (d d0 : Dom) (h : Valid d old) (hv : v.WF)
    (hw0 : HeapWF d0) (t : DTree) :
    Shows (patch old v d).2 (patch old v d).1.node t ↔ Shows (createElm v d0).2 (createElm v d0).1.node t := by
  have hp := (patch_correct old v d h hv).2.2.1
  have hc := createElm_shows v d0 hw0 hv
  constructor
  · intro ht; rw [← Shows.unique _ hp ht]; exact hc
  · intro ht; rw [← Shows.unique _ hc ht]; exact hp

end Snabbdom
