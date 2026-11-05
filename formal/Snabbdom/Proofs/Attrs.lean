import Snabbdom.Proofs.AttrList

namespace Snabbdom

theorem mem_of_lookup {β} {l : List (String × β)} {k : String} {v : β} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    by_cases e : k = k'
    · subst e; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (k == k') = false := by simp [e]
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_isSome {β} {l : List (String × β)} {kv : String × β} (h : kv ∈ l) :
    (l.lookup kv.1).isSome := by
  induction l with
  | nil => cases h
  | cons kv' rest ih =>
    obtain ⟨k', v'⟩ := kv'
    by_cases e : kv.1 = k'
    · simp [List.lookup, e]
    · have : (kv.1 == k') = false := by simp [e]
      simp only [List.lookup, this]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd rfl e
      · exact ih h

theorem eq_of_nodup_map {α β} {f : α → β} {l : List α} (h : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (e : f a = f b) : a = b := by
  induction l with
  | nil => cases ha
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem hb') h.1
    · exact absurd (e ▸ List.mem_map_of_mem ha') h.1
    · exact ih h.2 ha' hb'

theorem find_none (l : Attrs) (j : String) (h : j ∉ l.map (attrName ·.1)) :
    l.find? (fun kv => attrName kv.1 == j) = none :=
  List.find?_eq_none.2 fun kv hkv e => h (List.mem_map.2 ⟨kv, hkv, by simpa using e⟩)

theorem find_mem (l : Attrs) (hnd : (l.map (attrName ·.1)).Nodup) {kv : String × AttrVal} (h : kv ∈ l) :
    l.find? (fun kv' => attrName kv'.1 == attrName kv.1) = some kv := by
  cases ho : l.find? (fun kv' => attrName kv'.1 == attrName kv.1) with
  | none => exact absurd (by simp) (List.find?_eq_none.1 ho kv h)
  | some x =>
    exact congrArg some (eq_of_nodup_map hnd (List.mem_of_find?_eq_some ho) h
      (by simpa using List.find?_some ho))

/-- Writes `w kv` to the attribute `attrName kv.1`, for each entry `kv` that has one. -/
def writeAll {β} (w : String × AttrVal → Option (Option β)) (l : Attrs)
    (f : String → Option β) : String → Option β :=
  l.foldl (fun f kv => match w kv with | some o => overwrite (attrName kv.1) o f | none => f) f

theorem writeAll_apply {β} (w : String × AttrVal → Option (Option β)) (l : Attrs)
    (hnd : (l.map (attrName ·.1)).Nodup) (f : String → Option β) (j : String) :
    writeAll w l f j = match l.find? (fun kv => attrName kv.1 == j) with
      | some kv => (w kv).getD (f j)
      | none => f j := by
  induction l generalizing f with
  | nil => rfl
  | cons kv rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [writeAll, List.foldl_cons] at ih ⊢
    rw [ih hnd.2, List.find?_cons]
    by_cases hj : attrName kv.1 = j
    · subst hj
      rw [find_none rest _ hnd.1]
      cases hw : w kv <;> simp [overwrite, hw]
    · have : (attrName kv.1 == j) = false := by simp [hj]
      rw [this]
      have hj' : j ≠ attrName kv.1 := Ne.symm hj
      cases rest.find? (fun kv => attrName kv.1 == j) <;> cases w kv <;> simp [overwrite, hj']

/-- What key `k` with value `v` leaves at its qualified name. -/
def keyVal (k : String) (v : AttrVal) : Option (Option String × String) :=
  v.render.map (namespaceOf k, ·)

/-- The selector's `id` and `class`, which have no namespace. -/
def selView (s : Selector) : AttrView := fun j => (s.attr j).map (none, ·)

def setAll (a : Attrs) : AttrView → AttrView :=
  writeAll (fun kv => some (keyVal kv.1 kv.2)) a

theorem setAll_selector (sel : String) (a : Attrs) (h : AttrsWF a) :
    setAll a (selView (Selector.parse sel)) = renderAttrs sel a := by
  funext j
  rw [setAll, writeAll_apply _ a h.1]
  unfold renderAttrs Attrs.get
  cases a.find? (fun kv => attrName kv.1 == j) <;> rfl

/-- The removal loop of `updateAttrs`. -/
def dropAll (sel : String) (old new : Attrs) : AttrView → AttrView :=
  writeAll (fun kv => if (new.lookup kv.1).isNone then some (selView (Selector.parse sel) (attrName kv.1)) else none) old

/-- The setting loop of `updateAttrs`. -/
def changeAll (old new : Attrs) : AttrView → AttrView :=
  writeAll (fun kv => if old.lookup kv.1 ≠ some kv.2 then some (keyVal kv.1 kv.2) else none) new

theorem update_correct (sel : String) (old new : Attrs) (hold : AttrsWF old) (hnew : AttrsWF new) :
    changeAll old new (dropAll sel old new (renderAttrs sel old)) = renderAttrs sel new := by
  funext j
  rw [changeAll, writeAll_apply _ new hnew.1, dropAll, writeAll_apply _ old hold.1]
  unfold renderAttrs Attrs.get
  cases hn : new.find? (fun kv => attrName kv.1 == j) with
  | some kv =>
    have hk : attrName kv.1 = j := by simpa using List.find?_some hn
    subst hk
    by_cases hc : old.lookup kv.1 = some kv.2
    · have ho := find_mem old hold.1 (mem_of_lookup hc)
      have hs := lookup_isSome (List.mem_of_find?_eq_some hn)
      simp [hc, ho, Option.isSome_iff_ne_none.1 hs]
    · simp [hc, keyVal]
  | none =>
    cases ho : old.find? (fun kv => attrName kv.1 == j) with
    | none => rfl
    | some kv =>
      have hk : attrName kv.1 = j := by simpa using List.find?_some ho
      have hl : new.lookup kv.1 = none := by
        cases hl : new.lookup kv.1 with
        | none => rfl
        | some u => exact absurd (by simpa using hk) (List.find?_eq_none.1 hn _ (mem_of_lookup hl))
      simp [hl, hk, selView]

/-- A name that starts with `x` is neither `id` nor `class`. A namespaced key
starts with `x`, and so does its lowercase. -/
theorem Selector.attr_of_head (s : Selector) {k : String} (h : k.toList.head? = some 'x') :
    s.attr k = none := by
  have hi : k ≠ "id" := by rintro rfl; exact absurd h (by decide)
  have hc : k ≠ "class" := by rintro rfl; exact absurd h (by decide)
  simp [Selector.attr, hi, hc]

theorem asciiLower_head (k : String) :
    (asciiLower k).toList.head? = k.toList.head?.map Char.toLower := by
  simp [asciiLower, List.head?_map]

namespace Dom

/-- `d'` is `d` with only the attributes of `n` rewritten, by a function that
changes a tidy list as `g` changes its view. -/
structure AttrStep (d d' : Dom) (n : NodeId) (g : AttrView → AttrView) : Prop where
  step : ∃ f, (∀ m, d'.nodes m = if m = n then (d.nodes m).map (fun x => { x with attrs := f x.attrs }) else d.nodes m) ∧
    Realizes f g
  next : d'.next = d.next
  ok : d'.ok = d.ok

theorem AttrStep.modify (d : Dom) (n : NodeId) {f g} (h : Realizes f g) :
    AttrStep d (d.modifyAttrs n f) n g := ⟨⟨f, fun _ => rfl, h⟩, rfl, rfl⟩

theorem AttrStep.refl (d : Dom) (n : NodeId) : AttrStep d d n id :=
  ⟨⟨id, fun m => by split <;> (try subst m) <;> (try cases d.nodes _) <;> simp_all, Realizes.id⟩, rfl, rfl⟩

theorem AttrStep.trans {d1 d2 d3 : Dom} {n g1 g2} (h1 : AttrStep d1 d2 n g1) (h2 : AttrStep d2 d3 n g2) :
    AttrStep d1 d3 n (g2 ∘ g1) where
  step := by
    obtain ⟨f1, n1, r1⟩ := h1.step
    obtain ⟨f2, n2, r2⟩ := h2.step
    refine ⟨f2 ∘ f1, fun m => ?_, r1.comp r2⟩
    rw [n2, n1]
    split
    · cases d1.nodes m <;> simp
    · rfl
  next := by rw [h2.next, h1.next]
  ok := by rw [h2.ok, h1.ok]

theorem AttrStep.congr {d d' : Dom} {n g g'} (h : AttrStep d d' n g) (e : g = g') : AttrStep d d' n g' :=
  e ▸ h

theorem AttrStep.wf {d d' : Dom} {n g} (h : AttrStep d d' n g) (hw : HeapWF d) : HeapWF d' := by
  obtain ⟨f, hn', _⟩ := h.step
  have w := modify_wf (d := d) n (fun x => { x with attrs := f x.attrs }) (fun _ => ⟨rfl, rfl⟩) hw
  have hn : d'.nodes = (d.modify n fun x => { x with attrs := f x.attrs }).nodes := by
    funext m; rw [hn']; rfl
  exact ⟨fun i x hx => by rw [h.next]; exact w.bound i x (hn ▸ hx),
    fun p px c hp hc => by rw [hn] at hp ⊢; exact w.child_parent p px c hp hc,
    fun c cx p hc hcp => by rw [hn] at hc ⊢; exact w.parent_child c cx p hc hcp,
    fun p px hp => by rw [hn] at hp; exact w.nodup p px hp⟩

theorem AttrStep.other {d d' : Dom} {n g} (h : AttrStep d d' n g) (m : NodeId) (hm : m ≠ n) :
    d'.nodes m = d.nodes m := by
  obtain ⟨f, hn, _⟩ := h.step
  rw [hn, ite_eq_right hm]

/-- What an `AttrStep` does to node `n`. -/
theorem AttrStep.node {d d' : Dom} {n g} (h : AttrStep d d' n g) {x : DomNode} (hx : d.nodes n = some x) :
    ∃ l, d'.nodes n = some { x with attrs := l } ∧
      (Tidy x.attrs → Tidy l ∧ attrView l = g (attrView x.attrs)) := by
  obtain ⟨f, hn, hr⟩ := h.step
  exact ⟨f x.attrs, by rw [hn, ite_eq_left rfl, hx]; rfl, hr x.attrs⟩

theorem setAttr_step (d : Dom) (n : NodeId) (k v : String) (hk : namespaceOf (asciiLower k) = none) :
    AttrStep d (d.setAttr n k v) n (overwrite (asciiLower k) (some (none, v))) :=
  AttrStep.modify d n (setAttr_realizes k v hk)

theorem setKey_step (d : Dom) (n : NodeId) (k v : String) (hk : KeyOK k) :
    AttrStep d (setKey d n k v) n (overwrite (attrName k) (some (namespaceOf k, v))) := by
  unfold setKey attrName
  cases h : namespaceOf k with
  | none => exact AttrStep.modify d n (setAttr_realizes k v (hk h))
  | some ns => exact AttrStep.modify d n (setAttrNS_realizes k ns v h)

theorem removeKey_step (d : Dom) (n : NodeId) (k : String) :
    AttrStep d (removeKey d n k) n (overwrite (attrName k) none) := by
  unfold removeKey attrName
  cases h : namespaceOf k with
  | none => exact AttrStep.modify d n (removeAttr_realizes k)
  | some ns => exact AttrStep.modify d n (removeAttrNS_realizes k ns h)

theorem applyAttr_step (d : Dom) (n : NodeId) (k : String) (v : AttrVal) (hk : KeyOK k) :
    AttrStep d (applyAttr d n k v) n (overwrite (attrName k) (keyVal k v)) := by
  cases v with
  | str s => exact setKey_step d n k s hk
  | bool b => cases b with
    | false => exact removeKey_step d n k
    | true => exact setKey_step d n k "" hk

theorem dropAttr_step (sel : String) (d : Dom) (n : NodeId) (k : String) (hk : KeyOK k) :
    AttrStep d (dropAttr sel d n k) n
      (overwrite (attrName k) (selView (Selector.parse sel) (attrName k))) := by
  unfold dropAttr
  cases h : namespaceOf k with
  | none =>
    have ha : attrName k = asciiLower k := by simp [attrName, h]
    rw [ha]
    unfold selView
    cases hs : (Selector.parse sel).attr (asciiLower k) with
    | some v => exact setAttr_step d n k v (hk h)
    | none => have := removeKey_step d n k; rw [ha] at this; exact this
  | some ns =>
    have hx := namespaceOf_head h
    have hk : attrName k = k := by simp [attrName, h]
    have hr := removeKey_step d n k
    rw [hk] at hr
    rw [Selector.attr_of_head _ (by rw [asciiLower_head, hx]; rfl), hk, selView,
      Selector.attr_of_head _ hx]
    exact hr

theorem foldl_step (n : NodeId) (op : Dom → String × AttrVal → Dom)
    (w : String × AttrVal → Option (Option (Option String × String))) (l : Attrs)
    (hop : ∀ d, ∀ kv ∈ l, AttrStep d (op d kv) n
      (fun f => match w kv with | some o => overwrite (attrName kv.1) o f | none => f))
    (d : Dom) : AttrStep d (l.foldl op d) n (writeAll w l) := by
  induction l generalizing d with
  | nil => exact AttrStep.refl d n
  | cons kv rest ih =>
    exact ((hop d kv List.mem_cons_self).trans
      (ih (fun d kv' h => hop d kv' (List.mem_cons_of_mem _ h)) _)).congr (by funext f; simp only [writeAll, List.foldl_cons, Function.comp]; cases w kv <;> rfl)

theorem setAttrs_step (n : NodeId) (a : Attrs) (d : Dom) (ha : ∀ kv ∈ a, KeyOK kv.1) :
    AttrStep d (setAttrs n a d) n (setAll a) :=
  foldl_step n _ _ a (fun d kv h => applyAttr_step d n kv.1 kv.2 (ha kv h)) d

theorem updateAttrs_step (sel : String) (n : NodeId) (old new : Attrs) (d : Dom)
    (hold : ∀ kv ∈ old, KeyOK kv.1) (hnew : ∀ kv ∈ new, KeyOK kv.1) :
    AttrStep d (updateAttrs sel n old new d) n (changeAll old new ∘ dropAll sel old new) := by
  refine (foldl_step n _ _ old (fun d kv hm => ?_) d).trans
    (foldl_step n _ _ new (fun d kv hm => ?_) _)
  · by_cases hc : (new.lookup kv.1).isNone
    · simp only [hc, ite_true]; exact dropAttr_step sel d n kv.1 (hold kv hm)
    · simp only [hc]; exact AttrStep.refl d n
  · by_cases hc : old.lookup kv.1 = some kv.2
    · simp only [hc, ne_eq, not_true_eq_false, ite_false]; exact AttrStep.refl d n
    · simp only [hc, ne_eq, not_false_eq_true, ite_true]; exact applyAttr_step d n kv.1 kv.2 (hnew kv hm)

end Dom

theorem AttrsWF.keyOK {a : Attrs} (h : AttrsWF a) : ∀ kv ∈ a, KeyOK kv.1 :=
  fun kv hm => (h.2 kv hm).keyOK

theorem setSelectorAttrs_step (n : NodeId) (s : Selector) (d : Dom) :
    ∃ g, Dom.AttrStep d (setSelectorAttrs n s d) n g ∧ g (fun _ => none) = selView s := by
  have hid : asciiLower "id" = "id" := by decide
  have hcl : asciiLower "class" = "class" := by decide
  have nid : namespaceOf (asciiLower "id") = none := by rw [hid]; exact namespaceOf_of_no_colon (by simp)
  have ncl : namespaceOf (asciiLower "class") = none := by rw [hcl]; exact namespaceOf_of_no_colon (by simp)
  unfold setSelectorAttrs
  cases hi : s.id <;> cases hc : s.cls <;> dsimp only
  · exact ⟨id, Dom.AttrStep.refl d n, by funext j; simp [selView, Selector.attr, hi, hc]⟩
  · exact ⟨_, Dom.setAttr_step d n "class" _ ncl, by
      funext j; by_cases e : j = "class" <;> simp [overwrite, selView, Selector.attr, hi, hc, hcl, e]⟩
  · exact ⟨_, Dom.setAttr_step d n "id" _ nid, by
      funext j; by_cases e : j = "id" <;> simp [overwrite, selView, Selector.attr, hi, hc, hid, e]⟩
  · exact ⟨_, (Dom.setAttr_step d n "id" _ nid).trans (Dom.setAttr_step _ n "class" _ ncl), by
      funext j; by_cases e : j = "id" <;> by_cases e' : j = "class" <;>
        simp_all [overwrite, selView, Selector.attr]⟩

theorem moduleCreate_step (sel : String) (data : Data) (ch : List PNode) (n : NodeId) (d : Dom)
    (h : AttrsWF data.attrs) :
    Dom.AttrStep d (moduleCreate (.elem sel data ch n) d) n (setAll data.attrs) := by
  show Dom.AttrStep d (if data.attrs ≠ [] then setAttrs n data.attrs d else d) n _
  split
  · exact Dom.setAttrs_step n data.attrs d h.keyOK
  · rename_i h; simp only [ne_eq, Decidable.not_not] at h
    exact (Dom.AttrStep.refl d n).congr (by funext f; simp [h, setAll, writeAll])

theorem moduleUpdate_step (sel : String) (a : Data) (ch : List PNode) (n : NodeId)
    (sel' : String) (b : Data) (ch' : List VNode) (d : Dom) (ha : AttrsWF a.attrs) (hb : AttrsWF b.attrs) :
    ∃ g, Dom.AttrStep d (moduleUpdate (.elem sel a ch n) (.elem sel' b ch') d) n g ∧
      g (renderAttrs sel' a.attrs) = renderAttrs sel' b.attrs := by
  show ∃ g, Dom.AttrStep d (if a.attrs ≠ b.attrs then updateAttrs sel' n a.attrs b.attrs d else d) n g ∧ _
  split
  · exact ⟨_, Dom.updateAttrs_step sel' n a.attrs b.attrs d ha.keyOK hb.keyOK, update_correct sel' _ _ ha hb⟩
  · rename_i h; simp only [ne_eq, Decidable.not_not] at h
    exact ⟨id, Dom.AttrStep.refl d n, by rw [h]; rfl⟩

end Snabbdom
