/-
`place` only reads and rewrites the parent's child list, so its ordering
argument is made here on plain lists: `placeList R P cur L`, where `P` lists the
placements as `(anchored?, node)` and `R` holds every placed node.

The invariant, after processing a prefix `Q` of the placements with suffix
`P'` left, splits the child list at the cursor into `A ++ B`:
* the processed nodes `Q` are all in `A`, in order;
* none of them is in `B`;
* the anchored nodes still to process are all in `B`, in order.
Movable nodes still to process may be anywhere; they will be moved.
-/
import Snabbdom.Proofs.Basic

namespace Snabbdom

/-- `nextReconciledNode` on a list. -/
def nextReconciledIn (R L : List NodeId) : Option NodeId → Option NodeId
  | none => none
  | some o => (L.dropWhile (· ≠ o)).find? (· ∈ R)

def placeList (R : List NodeId) : List (Bool × NodeId) → Option NodeId → List NodeId → List NodeId
  | [], _, L => L
  | (true, c) :: rest, _, L => placeList R rest (after c L) L
  | (false, c) :: rest, cur, L =>
    let ref := nextReconciledIn R L cur
    if ref = some c then placeList R rest (after c L) L
    else placeList R rest ref (insertAt c ref (L.erase c))

def anchoredOf : List (Bool × NodeId) → List NodeId
  | [] => []
  | (true, c) :: rest => c :: anchoredOf rest
  | (false, _) :: rest => anchoredOf rest

def keepIn (S L : List NodeId) : List NodeId := L.filter (fun x => decide (x ∈ S))

theorem keepIn_append (S A B : List NodeId) : keepIn S (A ++ B) = keepIn S A ++ keepIn S B := by
  simp [keepIn, List.filter_append]

theorem keepIn_cons_mem (S L : List NodeId) (x : NodeId) (h : x ∈ S) : keepIn S (x :: L) = x :: keepIn S L := by
  simp [keepIn, h]

theorem keepIn_cons_not (S L : List NodeId) (x : NodeId) (h : x ∉ S) : keepIn S (x :: L) = keepIn S L := by
  simp [keepIn, h]

theorem mem_keepIn {S L : List NodeId} {x : NodeId} : x ∈ keepIn S L ↔ x ∈ L ∧ x ∈ S := by
  simp [keepIn]

theorem after_split (c : NodeId) (A B : List NodeId) (h : c ∉ A) :
    after c (A ++ c :: B) = B.head? := by
  induction A with
  | nil => simp [after]
  | cons a A ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, after, Ne.symm h.1, ite_false]
    exact ih h.2

theorem dropWhile_split (o : NodeId) (A B : List NodeId) (h : o ∉ A) :
    (A ++ o :: B).dropWhile (fun x => decide (x ≠ o)) = o :: B := by
  rw [List.dropWhile_append_of_pos (by intro a ha; simp; intro e; subst e; exact h ha)]
  simp [List.dropWhile]

theorem insertAt_split (n r : NodeId) (X Y : List NodeId) (h : r ∉ X) :
    insertAt n (some r) (X ++ r :: Y) = X ++ n :: r :: Y := by
  induction X with
  | nil => simp [insertAt]
  | cons x X ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, insertAt, Ne.symm h.1, ite_false, ih h.2]

theorem insertAt_none (n : NodeId) (L : List NodeId) : insertAt n none L = L ++ [n] := by
  cases L <;> rfl

theorem keepIn_nil_of (S L : List NodeId) (h : ∀ x ∈ L, x ∉ S) : keepIn S L = [] := by
  simp only [keepIn, List.filter_eq_nil_iff, decide_eq_true_eq]; exact h

theorem keepIn_congr (S S' L : List NodeId) (h : ∀ x ∈ L, (x ∈ S ↔ x ∈ S')) : keepIn S L = keepIn S' L := by
  simp only [keepIn]; apply List.filter_congr; intro x hx; simp [h x hx]

theorem keepIn_erase (S A : List NodeId) (c : NodeId) (hc : c ∉ S) (hA : A.Nodup) :
    keepIn S (A.erase c) = keepIn S A := by
  rw [hA.erase_eq_filter]
  simp only [keepIn, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : x ∈ S
  · have : x ≠ c := fun e => hc (e ▸ hx)
    simp [hx, this]
  · simp [hx]

theorem keepIn_of_sublist (S O : List NodeId) (hs : S.Sublist O) (hO : O.Nodup) : keepIn S O = S := by
  induction hs with
  | slnil => rfl
  | @cons l₁ l₂ a hs ih =>
    rw [List.nodup_cons] at hO
    have : a ∉ l₁ := fun h => hO.1 (hs.subset h)
    rw [keepIn_cons_not _ _ _ this, ih hO.2]
  | @cons_cons l₁ l₂ a hs ih =>
    rw [List.nodup_cons] at hO
    rw [keepIn_cons_mem _ _ _ (by simp)]
    congr 1
    calc keepIn (a :: l₁) l₂ = keepIn l₁ l₂ := keepIn_congr _ _ _ (fun x hx => by
            constructor
            · intro h; rcases List.mem_cons.1 h with rfl | h; exact absurd hx hO.1; exact h
            · exact List.mem_cons_of_mem _)
      _ = l₁ := ih hO.2

theorem keepIn_split_head (S B1 B2 T : List NodeId) (c : NodeId) (hcS : c ∈ S) (hc : c ∉ B1)
    (h : keepIn S (B1 ++ c :: B2) = c :: T) : keepIn S B1 = [] ∧ keepIn S B2 = T := by
  rw [keepIn_append, keepIn_cons_mem _ _ _ hcS] at h
  cases h1 : keepIn S B1 with
  | nil => rw [h1] at h; simp at h; exact ⟨rfl, h⟩
  | cons y ys =>
    rw [h1] at h; simp only [List.cons_append, List.cons.injEq] at h
    have : y ∈ keepIn S B1 := by rw [h1]; simp
    exact absurd (h.1 ▸ (mem_keepIn.1 this).1) hc

theorem anchoredOf_sublist : ∀ (P : List (Bool × NodeId)) (O : List NodeId),
    (∀ (i : Nat) (c : NodeId), P[i]? = some (true, c) → O[i]? = some c) → (anchoredOf P).Sublist O
  | [], _, _ => List.nil_sublist _
  | (b, c) :: P, [], h => by
    cases b
    · have := anchoredOf_sublist P [] (fun i c' hi => by
        have := h (i + 1) c' (by simpa using hi); simp at this)
      simpa [anchoredOf] using this
    · have := h 0 c (by simp); simp at this
  | (b, c) :: P, o :: O, h => by
    have ih := anchoredOf_sublist P O (fun i c' hi => by
      have := h (i + 1) c' (by simpa using hi); simpa using this)
    cases b
    · simp only [anchoredOf]; exact ih.cons o
    · have := h 0 c (by simp); simp at this; subst this
      simp only [anchoredOf]; exact ih.cons_cons _

theorem anchoredOf_subset : ∀ (P : List (Bool × NodeId)), ∀ x ∈ anchoredOf P, x ∈ P.map (·.2)
  | [], _, h => by simp [anchoredOf] at h
  | (b, c) :: P, x, h => by
    cases b
    · simp only [anchoredOf] at h; simp [anchoredOf_subset P x h]
    · simp only [anchoredOf, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · simp [anchoredOf_subset P x h]

structure PInv (Q : List NodeId) (P : List (Bool × NodeId)) (L : List NodeId)
    (cur : Option NodeId) : Prop where
  nodup : L.Nodup
  split : ∃ A B, L = A ++ B ∧ cur = B.head? ∧ keepIn Q A = Q ∧ (∀ x ∈ B, x ∉ Q) ∧
    keepIn (anchoredOf P) B = anchoredOf P

/-- The cursor moves past `c`, the first placed node after it. -/
theorem pinv_skip (Q : List NodeId) (c : NodeId) (P : List (Bool × NodeId)) (L : List NodeId)
    (A B1 B2 : List NodeId) (hL : L = A ++ (B1 ++ c :: B2)) (hnd : L.Nodup)
    (hA : keepIn Q A = Q) (hB : ∀ x ∈ B1 ++ c :: B2, x ∉ Q)
    (hB2 : keepIn (anchoredOf P) B2 = anchoredOf P) :
    PInv (Q ++ [c]) P L (after c L) := by
  have hnd' := hnd; rw [hL] at hnd'
  have hcA : c ∉ A := by
    intro h; rw [List.nodup_append] at hnd'; exact hnd'.2.2 c h c (by simp) rfl
  have hcB1 : c ∉ B1 := by
    intro h; rw [List.nodup_append, List.nodup_append] at hnd'
    exact hnd'.2.1.2.2 c h c (by simp) rfl
  have hcB2 : c ∉ B2 := by
    intro h; rw [List.nodup_append, List.nodup_append, List.nodup_cons] at hnd'
    exact hnd'.2.1.2.1.1 h
  refine ⟨hnd, A ++ B1 ++ [c], B2, by rw [hL]; simp, ?_, ?_, ?_, hB2⟩
  · rw [hL, ← List.append_assoc]; exact after_split c (A ++ B1) B2 (by simp [hcA, hcB1])
  · rw [keepIn_append, keepIn_append]
    have h1 : keepIn (Q ++ [c]) A = Q := by
      calc keepIn (Q ++ [c]) A = keepIn Q A := keepIn_congr _ _ _ (fun x hx => by
              simp only [List.mem_append, List.mem_singleton]
              constructor
              · rintro (h | rfl); exact h; exact absurd hx hcA
              · exact Or.inl)
        _ = Q := hA
    have h2 : keepIn (Q ++ [c]) B1 = [] := keepIn_nil_of _ _ (fun x hx => by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hB x (by simp [hx]), fun e => hcB1 (e ▸ hx)⟩)
    rw [h1, h2, keepIn_cons_mem _ _ _ (by simp)]; simp [keepIn]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hB x (by simp [hx]), fun e => hcB2 (e ▸ hx)⟩

theorem placeList_inv : ∀ (P : List (Bool × NodeId)) (Q L : List NodeId) (cur : Option NodeId)
    (R : List NodeId), R = Q ++ P.map (·.2) → R.Nodup → PInv Q P L cur →
    keepIn R (placeList R P cur L) = R ∧ (placeList R P cur L).Nodup
  | [], Q, L, cur, R, hR, _, inv => by
    obtain ⟨A, B, hL, _, hA, hB, _⟩ := inv.split
    simp only [List.map_nil, List.append_nil] at hR; subst hR
    refine ⟨?_, inv.nodup⟩
    simp only [placeList]; rw [hL, keepIn_append, hA, keepIn_nil_of _ _ hB]; simp
  | (true, c) :: P, Q, L, cur, R, hR, hRnd, inv => by
    obtain ⟨A, B, hL, hcur, hA, hB, hanch⟩ := inv.split
    simp only [anchoredOf] at hanch
    have hcB : c ∈ B := by
      have : c ∈ keepIn (c :: anchoredOf P) B := by rw [hanch]; simp
      exact (mem_keepIn.1 this).1
    obtain ⟨B1, B2, hBs⟩ := List.append_of_mem hcB
    have hnd := inv.nodup
    have hcB1 : c ∉ B1 := by
      rw [hL, hBs] at hnd; intro h; rw [List.nodup_append, List.nodup_append] at hnd
      exact hnd.2.1.2.2 c h c (by simp) rfl
    have hcB2 : c ∉ B2 := by
      rw [hL, hBs] at hnd; intro h; rw [List.nodup_append, List.nodup_append, List.nodup_cons] at hnd
      exact hnd.2.1.2.1.1 h
    rw [hBs] at hanch
    obtain ⟨_, h2⟩ := keepIn_split_head _ B1 B2 _ c (by simp) hcB1 hanch
    have hB2 : keepIn (anchoredOf P) B2 = anchoredOf P := by
      calc keepIn (anchoredOf P) B2 = keepIn (c :: anchoredOf P) B2 := keepIn_congr _ _ _ (fun x hx => by
              have : x ≠ c := fun e => hcB2 (e ▸ hx)
              simp [this])
        _ = anchoredOf P := h2
    have inv' := pinv_skip Q c P L A B1 B2 (by rw [hL, hBs]) hnd hA (by rw [← hBs]; exact hB) hB2
    simp only [placeList]
    exact placeList_inv P (Q ++ [c]) L _ R (by subst hR; simp) hRnd inv'
  | (false, c) :: P, Q, L, cur, R, hR, hRnd, inv => by
    obtain ⟨A, B, hL, hcur, hA, hB, hanch⟩ := inv.split
    simp only [anchoredOf] at hanch
    have hnd := inv.nodup
    have hcR : c ∈ R := by rw [hR]; simp
    have hcQ : c ∉ Q := by
      rw [hR] at hRnd; simp only [List.map_cons] at hRnd
      rw [List.nodup_append] at hRnd
      intro h; exact hRnd.2.2 c h c (by simp) rfl
    have hcP : c ∉ P.map (·.2) := by
      rw [hR] at hRnd; simp only [List.map_cons] at hRnd
      rw [List.nodup_append, List.nodup_cons] at hRnd; exact hRnd.2.1.1
    have hcanch : c ∉ anchoredOf P := fun h => hcP (anchoredOf_subset P c h)
    have hanchR : ∀ x ∈ anchoredOf P, x ∈ R := fun x hx => by rw [hR]; simp [anchoredOf_subset P x hx]
    have href : nextReconciledIn R L cur = B.find? (· ∈ R) := by
      cases B with
      | nil => simp at hcur; subst hcur; simp [nextReconciledIn]
      | cons o B' =>
        simp at hcur; subst hcur
        have hoA : o ∉ A := by
          rw [hL] at hnd; intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 o h o (by simp) rfl
        simp only [nextReconciledIn]; rw [hL, dropWhile_split o A B' hoA]
    simp only [placeList]
    rw [href]
    split
    · -- c is already in place
      rename_i heq
      obtain ⟨_, as, bs, hBs, has⟩ := List.find?_eq_some_iff_append.1 heq
      have hasR : ∀ x ∈ as, x ∉ R := fun x hx => by simpa using has x hx
      have hcas : c ∉ as := fun h => hasR c h hcR
      rw [hBs] at hanch
      have hbs : keepIn (anchoredOf P) bs = anchoredOf P := by
        rw [keepIn_append, keepIn_nil_of _ _ (fun x hx h => hasR x hx (hanchR x h)),
          keepIn_cons_not _ _ _ hcanch] at hanch
        simpa using hanch
      have inv' := pinv_skip Q c P L A as bs (by rw [hL, hBs]) hnd hA (by rw [← hBs]; exact hB) hbs
      exact placeList_inv P (Q ++ [c]) L _ R (by subst hR; simp) hRnd inv'
    · rename_i hne
      apply placeList_inv P (Q ++ [c]) _ _ R (by subst hR; simp) hRnd
      -- c moves in front of the reference node
      have hLe : L.erase c = A.erase c ++ B.erase c := by
        by_cases hcA : c ∈ A
        · rw [hL, List.erase_append_left _ hcA]
          have hcB : c ∉ B := by
            rw [hL] at hnd; intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 c hcA c h rfl
          rw [List.erase_of_not_mem hcB]
        · rw [hL, List.erase_append_right _ hcA, List.erase_of_not_mem hcA]
      have hndA : A.Nodup := by rw [hL] at hnd; exact (List.nodup_append.1 hnd).1
      have hndB : B.Nodup := by rw [hL] at hnd; exact (List.nodup_append.1 hnd).2.1
      have hcAe : c ∉ A.erase c := hndA.not_mem_erase
      have hAe : keepIn (Q ++ [c]) (A.erase c) = Q := by
        calc keepIn (Q ++ [c]) (A.erase c) = keepIn Q (A.erase c) := keepIn_congr _ _ _ (fun x hx => by
                simp only [List.mem_append, List.mem_singleton]
                constructor
                · rintro (h | rfl); exact h; exact absurd hx hcAe
                · exact Or.inl)
          _ = keepIn Q A := keepIn_erase Q A c hcQ hndA
          _ = Q := hA
      have hLe_nd : (L.erase c).Nodup := hnd.erase c
      have hL'nd : (insertAt c (B.find? (· ∈ R)) (L.erase c)).Nodup :=
        nodup_insertAt _ _ _ hLe_nd hnd.not_mem_erase
      cases hf : B.find? (· ∈ R) with
      | none =>
        rw [hf] at hL'nd
        have hBR : ∀ x ∈ B, x ∉ R := fun x hx => by
          have := List.find?_eq_none.1 hf x hx; simpa using this
        have hcB : c ∉ B := fun h => hBR c h hcR
        have hanchP : anchoredOf P = [] := by
          calc anchoredOf P = keepIn (anchoredOf P) B := hanch.symm
            _ = [] := keepIn_nil_of _ _ (fun x hx h => hBR x hx (hanchR x h))
        refine ⟨hL'nd, A.erase c ++ B ++ [c], [], ?_, rfl, ?_, by simp, by simp [hanchP, keepIn]⟩
        · rw [insertAt_none, hLe, List.erase_of_not_mem hcB]
          simp
        · rw [keepIn_append, keepIn_append, hAe,
            keepIn_nil_of _ _ (fun x hx h => hBR x hx (by
              rw [hR]; simp only [List.mem_append, List.mem_singleton] at h ⊢
              rcases h with h | h; exact Or.inl h; subst h; simp))]
          simp [keepIn]
      | some r =>
        rw [hf] at hL'nd hne
        obtain ⟨hrR, as, bs, hBs, has⟩ := List.find?_eq_some_iff_append.1 hf
        have hrR : r ∈ R := by simpa using hrR
        have hasR : ∀ x ∈ as, x ∉ R := fun x hx => by simpa using has x hx
        have hcr : c ≠ r := fun e => hne (by rw [e])
        have hcas : c ∉ as := fun h => hasR c h hcR
        have hBe : B.erase c = as ++ r :: bs.erase c := by
          rw [hBs, List.erase_append_right _ hcas, List.erase_cons_tail (by simpa using Ne.symm hcr)]
        have hrA : r ∉ A.erase c := by
          rw [hL, hBs] at hnd; intro h
          rw [List.nodup_append] at hnd
          exact hnd.2.2 r (List.mem_of_mem_erase h) r (by simp) rfl
        have hras : r ∉ as := fun h => hasR r h hrR
        refine ⟨hL'nd, A.erase c ++ as ++ [c], r :: bs.erase c, ?_, rfl, ?_, ?_, ?_⟩
        · rw [hLe, hBe, ← List.append_assoc, insertAt_split c r _ _ (by simp [hrA, hras])]
          simp
        · rw [keepIn_append, keepIn_append, hAe,
            keepIn_nil_of _ _ (fun x hx h => hasR x hx (by
              rw [hR]; simp only [List.mem_append, List.mem_singleton] at h ⊢
              rcases h with h | h; exact Or.inl h; subst h; simp))]
          simp [keepIn]
        · intro x hx
          simp only [List.mem_cons] at hx
          simp only [List.mem_append, List.mem_singleton, not_or]
          rcases hx with rfl | hx
          · exact ⟨hB x (by rw [hBs]; simp), Ne.symm hcr⟩
          · have hbsnd : bs.Nodup := by
              rw [hBs] at hndB; exact (List.nodup_cons.1 (List.nodup_append.1 hndB).2.1).2
            refine ⟨hB x (by rw [hBs]; simp [List.mem_of_mem_erase hx]), fun e => ?_⟩
            subst e; exact hbsnd.not_mem_erase hx
        · rw [hBs] at hanch
          rw [keepIn_append, keepIn_nil_of _ _ (fun x hx h => hasR x hx (hanchR x h))] at hanch
          rw [List.nil_append] at hanch
          have hbsnd : bs.Nodup := by
            rw [hBs] at hndB; exact (List.nodup_cons.1 (List.nodup_append.1 hndB).2.1).2
          refine Eq.trans ?_ hanch
          by_cases hr : r ∈ anchoredOf P
          · rw [keepIn_cons_mem _ _ _ hr, keepIn_cons_mem _ _ _ hr, keepIn_erase _ bs c hcanch hbsnd]
          · rw [keepIn_cons_not _ _ _ hr, keepIn_cons_not _ _ _ hr, keepIn_erase _ bs c hcanch hbsnd]

/-- The placed nodes end up in the child list in placement order. -/
theorem placeList_correct (O : List NodeId) (P : List (Bool × NodeId)) (hO : O.Nodup)
    (hR : (P.map (·.2)).Nodup) (hanch : ∀ (i : Nat) (c : NodeId), P[i]? = some (true, c) → O[i]? = some c) :
    keepIn (P.map (·.2)) (placeList (P.map (·.2)) P O.head? O) = P.map (·.2) ∧
      (placeList (P.map (·.2)) P O.head? O).Nodup := by
  apply placeList_inv P [] O O.head? _ (by simp) hR
  exact ⟨hO, [], O, by simp, rfl, rfl, by simp, keepIn_of_sublist _ _ (anchoredOf_sublist P O hanch) hO⟩

end Snabbdom
