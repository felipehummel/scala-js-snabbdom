/-
The DOM's attribute calls on an attribute list, read through `attrView`: on a
`Tidy` list, each one rewrites the view at a single qualified name.
-/
import Snabbdom.Proofs.Basic

namespace Snabbdom

def overwrite {β} (k : String) (o : Option β) (f : String → Option β) : String → Option β :=
  fun j => if j = k then o else f j

/-- One attribute per qualified name, each `Canon`. -/
def Tidy (l : List Attr) : Prop := (l.map Attr.qname).Nodup ∧ ∀ x ∈ l, x.Canon

theorem AttrsMirror.tidy {l : List Attr} {a : AttrView} (h : AttrsMirror l a) : Tidy l := ⟨h.1.1, h.2⟩

theorem AttrsMirror.of_tidy {l : List Attr} {a : AttrView} (h : Tidy l) (e : attrView l = a) :
    AttrsMirror l a := ⟨⟨h.1, e⟩, h.2⟩

/-- `f` changes a tidy list as `g` changes its view. -/
def Realizes (f : List Attr → List Attr) (g : AttrView → AttrView) : Prop :=
  ∀ l, Tidy l → Tidy (f l) ∧ attrView (f l) = g (attrView l)

theorem Realizes.id : Realizes id id := fun _ h => ⟨h, rfl⟩

theorem Realizes.comp {f1 f2 g1 g2} (h1 : Realizes f1 g1) (h2 : Realizes f2 g2) :
    Realizes (f2 ∘ f1) (g2 ∘ g1) := fun l h =>
  let ⟨t1, v1⟩ := h1 l h
  let ⟨t2, v2⟩ := h2 _ t1
  ⟨t2, by simp only [Function.comp, v2, v1]⟩

/-! ## Names -/

theorem toLower_eq_colon {c : Char} (h : c.toLower = ':') : c = ':' := by
  unfold Char.toLower at h
  split at h
  · rename_i hu
    simp at hu
    have := congrArg Char.toNat h
    simp at this
    have h2 : c.toNat = c.val.toNat := rfl
    have h3 : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 90 := by
      constructor
      · have := UInt32.le_iff_toNat_le.1 hu.1; simpa using this
      · have := UInt32.le_iff_toNat_le.1 hu.2; simpa using this
    omega
  · exact h

theorem colon_of_startsWith {q p : String} (h : q.startsWith p = true) (hp : ':' ∈ p.toList) :
    ':' ∈ q.toList := by
  obtain ⟨t, ht⟩ := String.startsWith_string_iff.1 h
  rw [← ht]; exact List.mem_append_left _ hp

theorem namespaceOf_of_no_colon {q : String} (h : ':' ∉ q.toList) : namespaceOf q = none := by
  unfold namespaceOf
  split
  · exact absurd (colon_of_startsWith (by assumption) (by decide)) h
  split
  · exact absurd (colon_of_startsWith (by assumption) (by decide)) h
  split
  · exact absurd (colon_of_startsWith (by assumption) (by decide)) h
  rfl

theorem namespaceOf_head {k ns : String} (h : namespaceOf k = some ns) : k.toList.head? = some 'x' := by
  unfold namespaceOf at h
  split at h
  · obtain ⟨t, ht⟩ := String.startsWith_string_iff.1 (by assumption); rw [← ht]; rfl
  split at h
  · obtain ⟨t, ht⟩ := String.startsWith_string_iff.1 (by assumption); rw [← ht]; rfl
  split at h
  · obtain ⟨t, ht⟩ := String.startsWith_string_iff.1 (by assumption); rw [← ht]; rfl
  cases h

theorem split_prefix (p : String) (t : List Char) (hp : ':' ∉ p.toList) :
    splitQName (String.ofList (p.toList ++ ':' :: t)) = (some p, String.ofList t) := by
  have : ∀ l : List Char, ':' ∉ l → splitAtColon (l ++ ':' :: t) = some (l, t) := by
    intro l hl
    induction l with
    | nil => simp [splitAtColon]
    | cons c cs ih =>
      have hc : c ≠ ':' := fun e => hl (e ▸ List.mem_cons_self)
      simp [splitAtColon, hc, ih (fun h => hl (List.mem_cons_of_mem _ h))]
  simp [splitQName, this _ hp]

theorem ofList_prefix (p : String) (t : List Char) :
    String.ofList (p.toList ++ ':' :: t) = p ++ ":" ++ String.ofList t := by
  apply String.toList_inj.1
  simp

/-- A key `namespaceOf` finds a namespace in is that namespace's prefix, a colon
and a local name, and `splitQName` splits it there. -/
theorem namespaceOf_some {k ns : String} (h : namespaceOf k = some ns) :
    splitQName k = (some (nsPrefix ns), (splitQName k).2) ∧ k = nsPrefix ns ++ ":" ++ (splitQName k).2 := by
  have key : ∀ p : String, ':' ∉ p.toList → k.startsWith (p ++ ":") = true →
      splitQName k = (some p, (splitQName k).2) ∧ k = p ++ ":" ++ (splitQName k).2 := by
    intro p hp hs
    obtain ⟨t, ht⟩ := String.startsWith_string_iff.1 hs
    have hk : k = String.ofList (p.toList ++ ':' :: t) := by
      rw [← String.ofList_toList (s := k), ← ht]; simp
    rw [hk, split_prefix p t hp]
    exact ⟨rfl, ofList_prefix p t⟩
  unfold namespaceOf at h
  split at h
  · cases h; exact key "xml" (by decide) (by assumption)
  split at h
  · cases h
    have : nsPrefix xmlnsNS = "xmlns" := by simp [nsPrefix, xmlnsNS, xmlNS]
    rw [this]; exact key "xmlns" (by decide) (by assumption)
  split at h
  · cases h
    have : nsPrefix xlinkNS = "xlink" := by simp [nsPrefix, xlinkNS, xmlnsNS, xmlNS]
    rw [this]; exact key "xlink" (by decide) (by assumption)
  cases h

theorem SafeName.no_colon {s : String} (h : SafeName s) : ':' ∉ s.toList := by
  unfold SafeName at h
  split at h
  · rename_i c cs hs
    rw [hs]
    rintro (_ | ⟨_, hm⟩)
    · exact absurd h.1 (by decide)
    · rcases h.2 ':' hm with h | h | h | h <;> revert h <;> decide
  · exact h.elim

theorem namespaceOf_append (p l : String) (hp : p ∈ ["xml", "xmlns", "xlink"]) :
    namespaceOf (p ++ ":" ++ l) ≠ none := by
  have hs : (p ++ ":" ++ l).startsWith (p ++ ":") = true :=
    String.startsWith_string_iff.2 ⟨l.toList, by simp⟩
  unfold namespaceOf
  split; · simp
  split; · simp
  split; · simp
  simp at hp
  rcases hp with rfl | rfl | rfl <;> simp_all

/-- What a key needs for `setAttribute` to leave a `Canon` attribute: one
without a namespace has none in its lowercase either. -/
def KeyOK (k : String) : Prop := namespaceOf k = none → namespaceOf (asciiLower k) = none

theorem AttrName.keyOK {k : String} (h : AttrName k) : KeyOK k := by
  intro hk
  rcases h with h | ⟨p, hp, l, _, rfl⟩
  · apply namespaceOf_of_no_colon
    intro hm
    simp only [asciiLower, String.toList_ofList, List.mem_map] at hm
    obtain ⟨c, hc, e⟩ := hm
    exact h.no_colon (toLower_eq_colon e ▸ hc)
  · exact absurd hk (namespaceOf_append p l hp)

/-! ## Attribute lists -/

theorem Attr.Canon.ns {a : Attr} (h : a.Canon) : namespaceOf a.qname = a.ns := by
  unfold Attr.Canon at h
  split at h
  · rename_i e; rw [e]; simp [Attr.qname, h.1, h.2]
  · rename_i e; rw [e]; exact h.2

theorem Attr.Canon.value {a : Attr} (v : String) (h : a.Canon) : ({ a with value := v } : Attr).Canon := h

theorem attrView_nil : attrView [] = fun _ => none := rfl

theorem attrView_cons (a : Attr) (l : List Attr) (j : String) :
    attrView (a :: l) j = if a.qname = j then some (a.ns, a.value) else attrView l j := by
  unfold attrView
  by_cases h : a.qname = j <;> simp [h]

theorem attrView_none {l : List Attr} {q : String} (h : q ∉ l.map Attr.qname) : attrView l q = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [attrView_cons]
    have : a.qname ≠ q := fun e => h (by simp [e])
    rw [ite_eq_right this]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

theorem tidy_cons {a : Attr} {l : List Attr} :
    Tidy (a :: l) ↔ a.Canon ∧ a.qname ∉ l.map Attr.qname ∧ Tidy l := by
  simp only [Tidy, List.map_cons, List.nodup_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h3, h1, h2, h4⟩
  · rintro ⟨h3, h1, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem removeFirst_sublist (p : Attr → Bool) (l : List Attr) : (removeFirst p l).Sublist l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    simp only [removeFirst]
    split
    · exact List.sublist_cons_self a l
    · exact ih.cons_cons a

theorem removeFirst_of_none (p : Attr → Bool) (l : List Attr) (h : ∀ x ∈ l, p x = false) :
    removeFirst p l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [removeFirst, h a List.mem_cons_self]
    simp only [Bool.false_eq_true, ite_false]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Removing the attribute named `q`, when `p` picks exactly the attributes named `q`. -/
theorem removeFirst_realizes (p : Attr → Bool) (q : String)
    (hp : ∀ x : Attr, x.Canon → (p x = true ↔ x.qname = q)) :
    Realizes (removeFirst p) (overwrite q none) := by
  intro l ht
  induction l with
  | nil => exact ⟨ht, by funext j; simp [removeFirst, overwrite, attrView_nil]⟩
  | cons a l ih =>
    obtain ⟨hc, hn, ht'⟩ := tidy_cons.1 ht
    simp only [removeFirst]
    by_cases hpa : p a = true
    · rw [ite_eq_left hpa]
      have hq := (hp a hc).1 hpa
      refine ⟨ht', ?_⟩
      funext j
      simp only [overwrite, attrView_cons]
      by_cases hj : j = q
      · subst hj; rw [ite_eq_left rfl]; exact attrView_none (hq ▸ hn)
      · rw [ite_eq_right hj, ite_eq_right (fun (e : a.qname = j) => hj (e ▸ hq))]
    · rw [ite_eq_right hpa]
      have hq : a.qname ≠ q := fun e => hpa ((hp a hc).2 e)
      obtain ⟨t1, v1⟩ := ih ht'
      refine ⟨tidy_cons.2 ⟨hc, fun hm => hn ?_, t1⟩, ?_⟩
      · exact ((removeFirst_sublist p l).map Attr.qname).subset hm
      · funext j
        simp only [attrView_cons, v1, overwrite]
        by_cases hj : j = q
        · subst hj; simp [hq]
        · simp [hj]

theorem mem_setFirst_qname (p : Attr → Bool) (v : String) (new : Attr) (l : List Attr) (x : String)
    (h : x ∈ (setFirst p v new l).map Attr.qname) : x = new.qname ∨ x ∈ l.map Attr.qname := by
  induction l with
  | nil => simp [setFirst] at h; exact Or.inl h
  | cons a l ih =>
    simp only [setFirst] at h
    split at h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h, Attr.qname])
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Setting the attribute named `q` to `v`, when `p` picks exactly the
attributes named `q`, an attribute already named `q` is in the namespace of
`new`, and `new` is named `q`. -/
theorem setFirst_realizes (p : Attr → Bool) (q v : String) (new : Attr)
    (hp : ∀ x : Attr, x.Canon → (p x = true ↔ x.qname = q))
    (hns : ∀ x : Attr, x.Canon → x.qname = q → x.ns = new.ns)
    (hq : new.qname = q) (hv : new.value = v) (hc : new.Canon) :
    Realizes (setFirst p v new) (overwrite q (some (new.ns, v))) := by
  intro l ht
  induction l with
  | nil =>
    refine ⟨tidy_cons.2 ⟨hc, by simp, ⟨List.nodup_nil, by simp⟩⟩, ?_⟩
    funext j
    simp only [setFirst, attrView_cons, overwrite, attrView_nil, hq, hv]
    by_cases hj : j = q
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  | cons a l ih =>
    obtain ⟨hca, hn, ht'⟩ := tidy_cons.1 ht
    simp only [setFirst]
    by_cases hpa : p a = true
    · rw [ite_eq_left hpa]
      have hqa := (hp a hca).1 hpa
      refine ⟨tidy_cons.2 ⟨hca.value v, by simpa [Attr.qname] using hn, ht'⟩, ?_⟩
      funext j
      have e1 : ({ a with value := v } : Attr).qname = a.qname := by simp [Attr.qname]
      simp only [attrView_cons, overwrite, e1, hqa]
      by_cases hj : j = q
      · subst hj; simp [hns a hca hqa]
      · simp [hj, Ne.symm hj]
    · rw [ite_eq_right hpa]
      have hqa : a.qname ≠ q := fun e => hpa ((hp a hca).2 e)
      obtain ⟨t1, v1⟩ := ih ht'
      refine ⟨tidy_cons.2 ⟨hca, fun hm => ?_, t1⟩, ?_⟩
      · rcases mem_setFirst_qname p v new l _ hm with h | h
        · exact hqa (h.trans hq)
        · exact hn h
      · funext j
        simp only [attrView_cons, v1, overwrite]
        by_cases hj : j = q
        · subst hj; simp [hqa]
        · simp [hj]

/-! ## The DOM calls -/

theorem setAttr_realizes (k v : String) (hk : namespaceOf (asciiLower k) = none) :
    Realizes (setFirst (·.qname == asciiLower k) v
        { ns := none, pfx := none, localName := asciiLower k, value := v })
      (overwrite (asciiLower k) (some (none, v))) :=
  setFirst_realizes _ _ _ _ (fun x _ => by simp)
    (fun x hx e => by have := hx.ns; rw [e, hk] at this; exact this.symm)
    rfl rfl ⟨rfl, hk⟩

theorem removeAttr_realizes (k : String) :
    Realizes (removeFirst (·.qname == asciiLower k)) (overwrite (asciiLower k) none) :=
  removeFirst_realizes _ _ (fun x _ => by simp)

/-- On a `Canon` attribute, matching the namespace and local name of key `k`
is having `k` as qualified name. -/
theorem ns_local_iff {k ns : String} (h : namespaceOf k = some ns) (x : Attr) (hx : x.Canon) :
    (x.ns == some ns && x.localName == (splitQName k).2) = true ↔ x.qname = k := by
  obtain ⟨_, hk⟩ := namespaceOf_some h
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hxn := hx.ns
  unfold Attr.Canon at hx
  split at hx
  · rename_i e
    constructor
    · rintro ⟨h1, _⟩; rw [e] at h1; cases h1
    · intro hq; rw [hq, h, e] at hxn; cases hxn
  · rename_i ns' e
    have hq : x.qname = nsPrefix ns' ++ ":" ++ x.localName := by simp [Attr.qname, hx.1]
    constructor
    · rintro ⟨h1, h2⟩
      rw [e] at h1; cases h1
      rw [hq, h2, ← hk]
    · intro hqk
      rw [hqk, h, e] at hxn; cases hxn
      refine ⟨e, ?_⟩
      rw [hq, hk] at hqk
      exact (String.append_right_inj _).1 hqk

theorem setAttrNS_realizes (k ns v : String) (h : namespaceOf k = some ns) :
    Realizes (setFirst (fun a => a.ns == some ns && a.localName == (splitQName k).2) v
        { ns := some ns, pfx := (splitQName k).1, localName := (splitQName k).2, value := v })
      (overwrite k (some (some ns, v))) := by
  obtain ⟨hs, hk⟩ := namespaceOf_some h
  have hq : ({ ns := some ns, pfx := (splitQName k).1, localName := (splitQName k).2, value := v } : Attr).qname = k := by
    simp only [Attr.qname]; rw [hs]; exact hk.symm
  refine setFirst_realizes _ _ _ _ (ns_local_iff h) (fun x hx e => ?_) hq rfl ⟨by rw [hs], by rw [hq, h]⟩
  have := ((ns_local_iff h) x hx).2 e
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem removeAttrNS_realizes (k ns : String) (h : namespaceOf k = some ns) :
    Realizes (removeFirst (fun a => a.ns == some ns && a.localName == (splitQName k).2))
      (overwrite k none) :=
  removeFirst_realizes _ _ (ns_local_iff h)

/-- The attribute with no namespace and a namespaced key as local name is never
`Canon`, so removing it changes nothing on a tidy list. -/
theorem removeNullNS_realizes (k ns : String) (h : namespaceOf k = some ns) :
    Realizes (removeFirst (fun a => a.ns == none && a.localName == k)) id := by
  intro l ht
  rw [removeFirst_of_none _ _ (fun x hx => ?_)]
  · exact ⟨ht, rfl⟩
  have hc := ht.2 x hx
  unfold Attr.Canon at hc
  split at hc
  · rename_i e
    simp only [e, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
    rintro rfl; rw [h] at hc; cases hc.2
  · rename_i e; simp [e]

end Snabbdom
