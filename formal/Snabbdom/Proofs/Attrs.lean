/-
The Attributes module: creating an element sets exactly the vnode's attributes,
and updating from the old attributes yields exactly the new ones.
-/
import Snabbdom.Proofs.Basic

namespace Snabbdom

/-! ### Pure part: attribute maps as functions -/

def setA (k : String) (o : Option String) (f : String → Option String) : String → Option String :=
  fun j => if j = k then o else f j

theorem lookup_eq_none {β} (l : List (String × β)) (k : String) (h : k ∉ l.map (·.1)) :
    l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k', v⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup]
    have : (k == k') = false := by simp [h.1]
    rw [this]; exact ih h.2

theorem lookup_cons_self {β} (k : String) (v : β) (rest : List (String × β)) :
    ((k, v) :: rest).lookup k = some v := by simp [List.lookup]

theorem lookup_cons_ne {β} (k j : String) (v : β) (rest : List (String × β)) (h : j ≠ k) :
    ((k, v) :: rest).lookup j = rest.lookup j := by
  simp only [List.lookup]
  have : (j == k) = false := by simp [h]
  rw [this]

/-- The attribute function after `setAttrs`. -/
def setAll (a : Attrs) (f : String → Option String) : String → Option String :=
  a.foldl (fun f kv => setA kv.1 kv.2.render f) f

theorem setAll_apply (a : Attrs) (hnd : (a.map (·.1)).Nodup) (f : String → Option String)
    (j : String) :
    setAll a f j = match a.lookup j with | some v => v.render | none => f j := by
  induction a generalizing f with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [setAll, List.foldl_cons] at ih ⊢
    rw [ih hnd.2]
    by_cases hj : j = k
    · subst hj
      rw [lookup_eq_none rest j hnd.1, lookup_cons_self]
      simp [setA]
    · rw [lookup_cons_ne k j v rest hj]
      cases rest.lookup j <;> simp [setA, hj]

theorem renderAttrs_eq (a : Attrs) (j : String) :
    renderAttrs a j = match a.lookup j with | some v => v.render | none => none := by
  unfold renderAttrs; cases a.lookup j <;> rfl

theorem setAll_empty (a : Attrs) (hnd : (a.map (·.1)).Nodup) :
    setAll a (fun _ => none) = renderAttrs a := by
  funext j; rw [setAll_apply a hnd, renderAttrs_eq]

/-- The attribute function after the first loop of `updateAttrs`. -/
def updNew (old new : Attrs) (f : String → Option String) : String → Option String :=
  new.foldl (fun f kv => if old.lookup kv.1 ≠ some kv.2 then setA kv.1 kv.2.render f else f) f

/-- ... and after the second loop. -/
def updOld (old new : Attrs) (f : String → Option String) : String → Option String :=
  old.foldl (fun f kv => if (new.lookup kv.1).isNone then setA kv.1 none f else f) f

theorem updNew_apply (old new : Attrs) (hnd : (new.map (·.1)).Nodup)
    (f : String → Option String) (j : String) :
    updNew old new f j = match new.lookup j with
      | some v => if old.lookup j ≠ some v then v.render else f j
      | none => f j := by
  induction new generalizing f with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [updNew, List.foldl_cons] at ih ⊢
    rw [ih hnd.2]
    by_cases hj : j = k
    · subst hj
      rw [lookup_eq_none rest j hnd.1, lookup_cons_self]
      by_cases hc : old.lookup j = some v <;> simp [setA, hc]
    · rw [lookup_cons_ne k j v rest hj]
      cases rest.lookup j <;> (by_cases hc : old.lookup k = some v <;> simp [setA, hj, hc])

theorem updOld_apply (old new : Attrs) (f : String → Option String) (j : String) :
    updOld old new f j =
      if j ∈ old.map (·.1) ∧ new.lookup j = none then none else f j := by
  induction old generalizing f with
  | nil => simp [updOld]
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp only [updOld, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hj : j = k
    · subst hj
      by_cases hn : new.lookup j = none <;> simp [setA, hn]
    · have hm : (j ∈ List.map (fun x => x.fst) ((k, v) :: rest)) ↔ j ∈ List.map (fun x => x.fst) rest := by
        simp [hj]
      simp only [hm]
      by_cases hn : (new.lookup k).isNone <;> simp [setA, hj, hn]

theorem update_correct (old new : Attrs) (hold : (old.map (·.1)).Nodup)
    (hnew : (new.map (·.1)).Nodup) :
    updOld old new (updNew old new (renderAttrs old)) = renderAttrs new := by
  funext j
  rw [updOld_apply, updNew_apply old new hnew, renderAttrs_eq new]
  cases hl : new.lookup j with
  | some v =>
    simp only [reduceCtorEq, and_false, ite_false]
    by_cases hc : old.lookup j = some v
    · simp [hc, renderAttrs, AttrVal.render]
    · simp [hc]
  | none =>
    simp only [and_true]
    split
    · rfl
    · rename_i hk
      rw [renderAttrs_eq, lookup_eq_none old j hk]

/-! ### Heap part -/

namespace Dom

/-- `d'` is `d` with only the attributes of `n` rewritten by `g`. -/
structure AttrStep (d d' : Dom) (n : NodeId) (g : (String → Option String) → String → Option String) : Prop where
  nodes : ∀ m, d'.nodes m = if m = n then (d.nodes m).map (fun x => { x with attrs := g x.attrs }) else d.nodes m
  next : d'.next = d.next
  ok : d'.ok = d.ok

theorem AttrStep.refl (d : Dom) (n : NodeId) : AttrStep d d n id :=
  ⟨fun m => by split <;> (try subst m) <;> (try cases d.nodes _) <;> simp_all, rfl, rfl⟩

theorem AttrStep.trans {d1 d2 d3 : Dom} {n g1 g2} (h1 : AttrStep d1 d2 n g1) (h2 : AttrStep d2 d3 n g2) :
    AttrStep d1 d3 n (g2 ∘ g1) where
  nodes m := by
    rw [h2.nodes, h1.nodes]
    split
    · cases d1.nodes m <;> simp
    · rfl
  next := by rw [h2.next, h1.next]
  ok := by rw [h2.ok, h1.ok]

theorem AttrStep.congr {d d' : Dom} {n g g'} (h : AttrStep d d' n g) (e : g = g') : AttrStep d d' n g' :=
  e ▸ h

theorem AttrStep.wf {d d' : Dom} {n g} (h : AttrStep d d' n g) (hw : HeapWF d) : HeapWF d' := by
  have w := modify_wf (d := d) n (fun x => { x with attrs := g x.attrs }) (fun _ => ⟨rfl, rfl⟩) hw
  have hn : d'.nodes = (d.modify n fun x => { x with attrs := g x.attrs }).nodes := by
    funext m; rw [h.nodes]; rfl
  exact ⟨fun i x hx => by rw [h.next]; exact w.bound i x (hn ▸ hx),
    fun p px c hp hc => by rw [hn] at hp ⊢; exact w.child_parent p px c hp hc,
    fun c cx p hc hcp => by rw [hn] at hc ⊢; exact w.parent_child c cx p hc hcp,
    fun p px hp => by rw [hn] at hp; exact w.nodup p px hp⟩

/-- Outside `n`, an attribute step changes nothing. -/
theorem AttrStep.other {d d' : Dom} {n g} (h : AttrStep d d' n g) (m : NodeId) (hm : m ≠ n) :
    d'.nodes m = d.nodes m := by rw [h.nodes, ite_eq_right hm]

theorem applyAttr_step (d : Dom) (n : NodeId) (k : String) (v : AttrVal) :
    AttrStep d (applyAttr d n k v) n (setA k v.render) := by
  refine ⟨fun m => ?_, ?_, ?_⟩
  all_goals (cases v with
    | str s => rfl
    | bool b => cases b <;> rfl)

theorem setAttrs_step (n : NodeId) (a : Attrs) (d : Dom) :
    AttrStep d (setAttrs n a d) n (setAll a) := by
  induction a generalizing d with
  | nil => exact AttrStep.refl d n
  | cons kv rest ih =>
    have := (applyAttr_step d n kv.1 kv.2).trans (ih (applyAttr d n kv.1 kv.2))
    exact this.congr (by funext f; rfl)

theorem updateAttrs_step (n : NodeId) (old new : Attrs) (d : Dom) :
    AttrStep d (updateAttrs n old new d) n (updOld old new ∘ updNew old new) := by
  have s1 : ∀ (l : Attrs) (d : Dom), AttrStep d
      (l.foldl (fun d kv => if old.lookup kv.1 ≠ some kv.2 then applyAttr d n kv.1 kv.2 else d) d) n
      (fun f => l.foldl (fun f kv => if old.lookup kv.1 ≠ some kv.2 then setA kv.1 kv.2.render f else f) f) := by
    intro l
    induction l with
    | nil => intro d; exact AttrStep.refl d n
    | cons kv rest ih =>
      intro d
      simp only [List.foldl_cons]
      by_cases hc : old.lookup kv.1 ≠ some kv.2
      · simp only [hc, ite_true, ne_eq, not_false_eq_true]
        exact ((applyAttr_step d n kv.1 kv.2).trans (ih _)).congr (by funext f; simp [hc])
      · simp only [hc, ite_false]
        exact ((AttrStep.refl d n).trans (ih d)).congr (by funext f; simp [hc])
  have s2 : ∀ (l : Attrs) (d : Dom), AttrStep d
      (l.foldl (fun d kv => if (new.lookup kv.1).isNone then d.removeAttr n kv.1 else d) d) n
      (fun f => l.foldl (fun f kv => if (new.lookup kv.1).isNone then setA kv.1 none f else f) f) := by
    intro l
    induction l with
    | nil => intro d; exact AttrStep.refl d n
    | cons kv rest ih =>
      intro d
      simp only [List.foldl_cons]
      by_cases hc : (new.lookup kv.1).isNone
      · simp only [hc, ite_true]
        exact ((⟨fun _ => rfl, rfl, rfl⟩ : AttrStep d (d.removeAttr n kv.1) n (setA kv.1 none)).trans
          (ih _)).congr (by funext f; simp [hc])
      · simp only [hc, ite_false]
        exact ((AttrStep.refl d n).trans (ih d)).congr (by funext f; simp [hc])
  exact ((s1 new d).trans (s2 old _)).congr rfl

end Dom

/-! ### The module hooks -/

theorem moduleCreate_step (sel : String) (data : Data) (ch : List PNode) (n : NodeId) (d : Dom) :
    Dom.AttrStep d (moduleCreate (.elem sel data ch n) d) n (setAll data.attrs) := by
  show Dom.AttrStep d (if data.attrs ≠ [] then setAttrs n data.attrs d else d) n _
  split
  · exact Dom.setAttrs_step n data.attrs d
  · rename_i h; simp only [ne_eq, Decidable.not_not] at h
    exact (Dom.AttrStep.refl d n).congr (by funext f; simp [h, setAll])

theorem moduleUpdate_step (sel : String) (a : Data) (ch : List PNode) (n : NodeId)
    (sel' : String) (b : Data) (ch' : List VNode) (d : Dom) :
    ∃ g, Dom.AttrStep d (moduleUpdate (.elem sel a ch n) (.elem sel' b ch') d) n g ∧
      ((a.attrs.map (·.1)).Nodup → (b.attrs.map (·.1)).Nodup →
        g (renderAttrs a.attrs) = renderAttrs b.attrs) := by
  show ∃ g, Dom.AttrStep d (if a.attrs ≠ b.attrs then updateAttrs n a.attrs b.attrs d else d) n g ∧ _
  split
  · exact ⟨_, Dom.updateAttrs_step n a.attrs b.attrs d, fun h1 h2 => update_correct _ _ h1 h2⟩
  · rename_i h; simp only [ne_eq, Decidable.not_not] at h
    exact ⟨id, Dom.AttrStep.refl d n, fun _ _ => by rw [h]; rfl⟩

end Snabbdom
