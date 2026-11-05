import Snabbdom.Spec

namespace Snabbdom

theorem mem_insertAt (n : NodeId) (ref : Option NodeId) (l : List NodeId) (x : NodeId) :
    x ∈ insertAt n ref l ↔ x = n ∨ x ∈ l := by
  induction l with
  | nil => cases ref <;> simp [insertAt]
  | cons y ys ih =>
    cases ref with
    | none => simp [insertAt]; grind
    | some r =>
      simp only [insertAt]
      split
      · simp
      · simp only [List.mem_cons, ih]; grind

theorem nodup_insertAt (n : NodeId) (ref : Option NodeId) (l : List NodeId)
    (hl : l.Nodup) (hn : n ∉ l) : (insertAt n ref l).Nodup := by
  induction l with
  | nil => cases ref <;> simp [insertAt]
  | cons y ys ih =>
    have hys : n ∉ ys := fun h => hn (List.mem_cons_of_mem _ h)
    have hny : n ≠ y := fun h => hn (h ▸ List.mem_cons_self)
    cases ref with
    | none =>
      simp only [insertAt]
      rw [List.nodup_append]
      refine ⟨hl, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hn ha
    | some r =>
      simp only [insertAt]
      split
      · exact List.nodup_cons.2 ⟨hn, hl⟩
      · refine List.nodup_cons.2 ⟨?_, ih (List.nodup_cons.1 hl).2 hys⟩
        rw [mem_insertAt]; rintro (h | h)
        · exact hny h.symm
        · exact (List.nodup_cons.1 hl).1 h

namespace Dom

variable {d : Dom}

@[simp] theorem get_eq (n : NodeId) : d.get n = d.nodes n := rfl
@[simp] theorem nodes_modify (n m : NodeId) (f : DomNode → DomNode) :
    (d.modify n f).nodes m = if m = n then (d.nodes m).map f else d.nodes m := rfl
@[simp] theorem next_modify (n : NodeId) (f) : (d.modify n f).next = d.next := rfl
@[simp] theorem ok_modify (n : NodeId) (f) : (d.modify n f).ok = d.ok := rfl
@[simp] theorem nodes_log (op) : (d.log op).nodes = d.nodes := rfl
@[simp] theorem next_log (op) : (d.log op).next = d.next := rfl
@[simp] theorem ok_log (op) : (d.log op).ok = d.ok := rfl
@[simp] theorem nodes_fail : d.fail.nodes = d.nodes := rfl
@[simp] theorem next_fail : d.fail.next = d.next := rfl
@[simp] theorem ok_fail : d.fail.ok = false := rfl

theorem parentNode_eq (n : NodeId) : d.parentNode n = (d.nodes n).bind (·.parent) := rfl

theorem log_wf (op) (h : HeapWF d) : HeapWF (d.log op) := ⟨h.1, h.2, h.3, h.4⟩

/-! ### Allocation -/

theorem alloc_fst (k : Kind) : (d.alloc k).1 = d.next := rfl
@[simp] theorem alloc_next (k : Kind) : (d.alloc k).2.next = d.next + 1 := rfl
@[simp] theorem alloc_ok (k : Kind) : (d.alloc k).2.ok = d.ok := rfl
theorem alloc_nodes (k : Kind) (m : NodeId) :
    (d.alloc k).2.nodes m = if m = d.next then some { kind := k } else d.nodes m := rfl

theorem alloc_wf (k : Kind) (h : HeapWF d) : HeapWF (d.alloc k).2 where
  bound i x hx := by
    have := h.bound; simp only [alloc_nodes, alloc_next] at *; grind
  child_parent p px c hp hc := by
    have := h.child_parent; have := h.bound; simp only [alloc_nodes] at *; grind
  parent_child c cx p hc hcp := by
    have := h.parent_child; have := h.bound; simp only [alloc_nodes] at *; grind
  nodup p px hp := by
    have := h.nodup; simp only [alloc_nodes] at *; split at hp <;> grind

theorem alloc_nodes_old (k : Kind) (m : NodeId) (hm : m < d.next) :
    (d.alloc k).2.nodes m = d.nodes m := by
  rw [alloc_nodes, ite_eq_right (by omega : ¬ _)]

/-! ### Changes that keep children and parents -/

theorem modify_wf (n : NodeId) (f : DomNode → DomNode)
    (hf : ∀ x, (f x).children = x.children ∧ (f x).parent = x.parent) (h : HeapWF d) :
    HeapWF (d.modify n f) where
  bound i x hx := by
    simp only [nodes_modify, next_modify] at *
    split at hx
    · cases hd : d.nodes i <;> simp [hd] at hx; exact h.bound i _ hd
    · exact h.bound i x hx
  child_parent p px c hp hc := by
    simp only [nodes_modify] at *
    have back : ∃ y, d.nodes p = some y ∧ y.children = px.children := by
      split at hp
      · cases hd : d.nodes p <;> simp [hd] at hp
        exact ⟨_, rfl, by rw [← hp, (hf _).1]⟩
      · exact ⟨px, hp, rfl⟩
    obtain ⟨y, hy, hyc⟩ := back
    obtain ⟨cx, hcx, hcp⟩ := h.child_parent p y c hy (hyc ▸ hc)
    split
    · rename_i hcn; subst hcn; exact ⟨f cx, by simp [hcx], (hf cx).2 ▸ hcp⟩
    · exact ⟨cx, hcx, hcp⟩
  parent_child c cx p hc hcp := by
    simp only [nodes_modify] at *
    have back : ∃ y, d.nodes c = some y ∧ y.parent = cx.parent := by
      split at hc
      · cases hd : d.nodes c <;> simp [hd] at hc
        exact ⟨_, rfl, by rw [← hc, (hf _).2]⟩
      · exact ⟨cx, hc, rfl⟩
    obtain ⟨y, hy, hyp⟩ := back
    obtain ⟨px, hpx, hm⟩ := h.parent_child c y p hy (hyp ▸ hcp)
    split
    · rename_i hpn; subst hpn; exact ⟨f px, by simp [hpx], (hf px).1 ▸ hm⟩
    · exact ⟨px, hpx, hm⟩
  nodup p px hp := by
    simp only [nodes_modify] at hp
    split at hp
    · cases hd : d.nodes p <;> simp [hd] at hp
      rw [← hp, (hf _).1]; exact h.nodup p _ hd
    · exact h.nodup p px hp

@[simp] theorem setAttr_nodes (n : NodeId) (k v : String) (m : NodeId) :
    (d.setAttr n k v).nodes m = if m = n then (d.nodes m).map
      (fun x => { x with attrs := fun j => if j = attrName k then some v else x.attrs j }) else d.nodes m := rfl
@[simp] theorem setAttr_next (n k v) : (d.setAttr n k v).next = d.next := rfl
@[simp] theorem setAttr_ok (n k v) : (d.setAttr n k v).ok = d.ok := rfl
@[simp] theorem removeAttr_nodes (n : NodeId) (k : String) (m : NodeId) :
    (d.removeAttr n k).nodes m = if m = n then (d.nodes m).map
      (fun x => { x with attrs := fun j => if j = attrName k then none else x.attrs j }) else d.nodes m := rfl
@[simp] theorem removeAttr_next (n k) : (d.removeAttr n k).next = d.next := rfl
@[simp] theorem removeAttr_ok (n k) : (d.removeAttr n k).ok = d.ok := rfl

theorem setAttr_wf (n k v) (h : HeapWF d) : HeapWF (d.setAttr n k v) :=
  modify_wf n _ (fun _ => ⟨rfl, rfl⟩) h
theorem removeAttr_wf (n k) (h : HeapWF d) : HeapWF (d.removeAttr n k) :=
  modify_wf n _ (fun _ => ⟨rfl, rfl⟩) h

/-! ### setText -/

theorem setText_text (n : NodeId) (s t : String) (x : DomNode) (hx : d.nodes n = some x)
    (hk : x.kind = .text t) :
    d.setText n s = (d.log (.setText n s)).modify n fun x => { x with kind := .text s } := by
  unfold setText
  simp only [get_eq, nodes_log, hx]
  cases x; simp only at hk; subst hk; rfl

theorem setText_comment (n : NodeId) (s t : String) (x : DomNode) (hx : d.nodes n = some x)
    (hk : x.kind = .comment t) :
    d.setText n s = (d.log (.setText n s)).modify n fun x => { x with kind := .comment s } := by
  unfold setText
  simp only [get_eq, nodes_log, hx]
  cases x; simp only at hk; subst hk; rfl

/-! ### Pre-insert (insertBefore / appendChild) -/

/-- The precondition snabbdom always meets: `n` is detached or already a child
of `p`, and `ref` is another child of `p`. -/
structure InsertOk (d : Dom) (p n : NodeId) (ref : Option NodeId) (px nx : DomNode) : Prop where
  hp : d.nodes p = some px
  hn : d.nodes n = some nx
  ne : n ≠ p
  parent : nx.parent = none ∨ nx.parent = some p
  ref_ok : ∀ r, ref = some r → r ∈ px.children ∧ r ≠ n

theorem InsertOk.not_mem {p n : NodeId} {ref} {px nx : DomNode} (h : HeapWF d)
    (hi : InsertOk d p n ref px nx) (hpar : nx.parent = none) : n ∉ px.children := by
  intro hm
  obtain ⟨cx, hcx, hcp⟩ := h.child_parent p px n hi.hp hm
  rw [hi.hn] at hcx; cases hcx; rw [hpar] at hcp; cases hcp

theorem preInsert_nodes {p n : NodeId} {ref : Option NodeId} {px nx : DomNode}
    (h : HeapWF d) (hi : InsertOk d p n ref px nx) (m : NodeId) :
    (d.preInsert p n ref).nodes m =
      if m = p then some { px with children := insertAt n ref (px.children.erase n) }
      else if m = n then some { nx with parent := some p }
      else d.nodes m := by
  have hrefne : (if ref = some n then d.nextSibling n else ref) = ref := by
    cases ref with
    | none => simp
    | some r =>
      have := (hi.ref_ok r rfl).2
      simp [this]
  have hvalid : refValid px.children ref = true := by
    cases ref with
    | none => rfl
    | some r => simp [refValid, (hi.ref_ok r rfl).1]
  unfold preInsert
  simp only [get_eq, hi.hp, hi.hn, hvalid, Bool.not_true, Bool.false_eq_true, ite_false, hrefne]
  unfold detach
  have hne := hi.ne
  rcases hi.parent with hpar | hpar
  · have hnot := hi.not_mem h hpar
    simp only [parentNode_eq, hi.hn, Option.bind_some, hpar, nodes_modify,
      List.erase_of_not_mem hnot]
    by_cases hmp : m = p
    · subst hmp; simp [hi.hp, Ne.symm hne]
    · by_cases hmn : m = n
      · subst hmn; simp [hmp, hi.hn]
      · simp [hmp, hmn]
  · simp only [parentNode_eq, hi.hn, Option.bind_some, hpar, nodes_modify]
    by_cases hmp : m = p
    · subst hmp; simp [hi.hp, Ne.symm hne]
    · by_cases hmn : m = n
      · subst hmn; simp [hmp, hi.hn]
      · simp [hmp, hmn]

@[simp] theorem preInsert_next (p n : NodeId) (ref) : (d.preInsert p n ref).next = d.next := by
  unfold preInsert detach
  repeat' split
  all_goals simp

theorem preInsert_ok {p n : NodeId} {ref : Option NodeId} {px nx : DomNode}
    (hi : InsertOk d p n ref px nx) : (d.preInsert p n ref).ok = d.ok := by
  have hvalid : refValid px.children ref = true := by
    cases ref with
    | none => rfl
    | some r => simp [refValid, (hi.ref_ok r rfl).1]
  unfold preInsert detach
  simp only [get_eq, hi.hp, hi.hn, hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
  split <;> simp

theorem preInsert_wf {p n : NodeId} {ref : Option NodeId} {px nx : DomNode}
    (h : HeapWF d) (hi : InsertOk d p n ref px nx) : HeapWF (d.preInsert p n ref) := by
  have hN := preInsert_nodes h hi
  have hp := hi.hp; have hn := hi.hn; have hne := hi.ne; have hpar := hi.parent
  have cp := h.child_parent; have pc := h.parent_child; have nd := h.nodup; have bd := h.bound
  have mi := mem_insertAt n ref
  have ndp := h.nodup p px hp
  constructor
  · intro i x hx
    rw [hN] at hx; simp only [preInsert_next]; grind
  · intro q qx c hq hc
    rw [hN] at hq
    simp only [hN]
    by_cases hqp : q = p
    · subst hqp
      simp at hq; subst hq
      rw [mi] at hc
      rcases hc with rfl | hc
      · exact ⟨{ nx with parent := some q }, by simp [hne], rfl⟩
      · have hcn : c ≠ n := fun e => by subst e; exact ndp.not_mem_erase hc
        obtain ⟨cx, hcx, hcp⟩ := cp q px c hp (List.mem_of_mem_erase hc)
        grind
    · grind
  · intro c cx q hc hcq
    rw [hN] at hc
    simp only [hN]
    by_cases hcp : c = p
    · subst hcp; simp at hc; subst hc
      obtain ⟨qx, hqx, hm⟩ := pc c px q hp hcq
      by_cases hqn : q = n
      · -- p is a child of n: the DOM would throw HierarchyRequestError,
        -- which is not modeled; the heap stays well formed anyway
        subst hqn; rw [hn] at hqx; cases hqx
        exact ⟨{ nx with parent := some c }, by simp [hne], hm⟩
      · grind
    · by_cases hcn : c = n
      · subst hcn; simp [hcp] at hc; subst hc; simp at hcq; subst hcq
        simp [mi]
      · simp [hcp, hcn] at hc
        obtain ⟨qx, hqx, hm⟩ := pc c cx q hc hcq
        by_cases hqp : q = p
        · subst hqp; simp [mi]; rw [hp] at hqx; cases hqx
          exact Or.inr ((List.mem_erase_of_ne hcn).2 hm)
        · by_cases hqn : q = n
          · subst hqn; simp [hqp]; rw [hn] at hqx; cases hqx; exact hm
          · simp [hqp, hqn, hqx, hm]
  · intro q qx hq
    rw [hN] at hq
    split at hq
    · cases hq
      exact nodup_insertAt _ _ _ (ndp.erase n) ndp.not_mem_erase
    · split at hq
      · cases hq; exact nd n nx hn
      · exact nd q qx hq

/-! ### removeChild -/

theorem removeChild_nodes {p c : NodeId} {px cx : DomNode} (hp : d.nodes p = some px)
    (hc : d.nodes c = some cx) (hm : c ∈ px.children) (hne : c ≠ p) (m : NodeId) :
    (d.removeChild p c).nodes m =
      if m = p then some { px with children := px.children.erase c }
      else if m = c then some { cx with parent := none }
      else d.nodes m := by
  unfold removeChild
  simp only [get_eq, nodes_log, hp, hm, ite_true, nodes_modify]
  by_cases hmp : m = p
  · subst hmp; simp [hp, Ne.symm hne]
  · by_cases hmc : m = c
    · subst hmc; simp [hmp, hc]
    · simp [hmp, hmc]

theorem removeChild_next (p c : NodeId) : (d.removeChild p c).next = d.next := by
  unfold removeChild; simp only [get_eq, nodes_log]; repeat' split
  all_goals simp

theorem removeChild_ok {p c : NodeId} {px : DomNode} (hp : d.nodes p = some px)
    (hm : c ∈ px.children) : (d.removeChild p c).ok = d.ok := by
  unfold removeChild; simp [hp, hm]

theorem removeChild_wf {p c : NodeId} {px cx : DomNode} (h : HeapWF d)
    (hp : d.nodes p = some px) (hc : d.nodes c = some cx) (hm : c ∈ px.children) (hne : c ≠ p) :
    HeapWF (d.removeChild p c) := by
  have hN := removeChild_nodes hp hc hm hne
  have cp := h.child_parent; have pc := h.parent_child; have nd := h.nodup; have bd := h.bound
  have ndp := nd p px hp
  have hcpar : cx.parent = some p := by
    obtain ⟨y, hy, hyp⟩ := cp p px c hp hm; rw [hc] at hy; cases hy; exact hyp
  constructor
  · intro i x hx; rw [hN] at hx; rw [removeChild_next]; grind
  · intro q qx k hq hk
    rw [hN] at hq; simp only [hN]
    by_cases hqp : q = p
    · subst hqp; simp at hq; subst hq
      have hkc : k ≠ c := fun e => by subst e; exact ndp.not_mem_erase hk
      obtain ⟨kx, hkx, hkp⟩ := cp q px k hp (List.mem_of_mem_erase hk)
      grind
    · by_cases hqc : q = c
      · subst hqc; simp [hqp] at hq; subst hq
        obtain ⟨kx, hkx, hkp⟩ := cp q cx k hc hk
        grind
      · simp [hqp, hqc] at hq
        obtain ⟨kx, hkx, hkp⟩ := cp q qx k hq hk
        grind
  · intro k kx q hk hkq
    rw [hN] at hk; simp only [hN]
    by_cases hkp : k = p
    · subst hkp; simp at hk; subst hk
      obtain ⟨qx, hqx, hm'⟩ := pc k px q hp hkq
      grind
    · by_cases hkc : k = c
      · subst hkc; simp [hkp] at hk; subst hk; simp at hkq
      · simp [hkp, hkc] at hk
        obtain ⟨qx, hqx, hm'⟩ := pc k kx q hk hkq
        by_cases hqp : q = p
        · subst hqp; rw [hp] at hqx; cases hqx; simp
          exact (List.mem_erase_of_ne hkc).2 hm'
        · by_cases hqc : q = c
          · subst hqc; rw [hc] at hqx; cases hqx; simp [hqp]; exact hm'
          · simp [hqp, hqc, hqx, hm']
  · intro q qx hq
    rw [hN] at hq
    split at hq
    · cases hq; exact ndp.erase c
    · split at hq
      · cases hq; exact nd c cx hc
      · exact nd q qx hq

end Dom
end Snabbdom
