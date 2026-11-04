/-
The reordering done by `place` (init.scala:257), on plain lists.

`placeL R P cur L` is `place` with the parent's child list `L` as the only
state. `P` lists the placements in order as `(anchored?, node)`; `R` is the
list of all placed nodes.

Main result (`placeL_correct`): if anchored placement `i` is old child `i`,
then afterwards the placed nodes appear in the child list exactly in the order
of `P`.

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
def refOf (R L : List NodeId) : Option NodeId → Option NodeId
  | none => none
  | some o => (L.dropWhile (· ≠ o)).find? (· ∈ R)

def placeL (R : List NodeId) : List (Bool × NodeId) → Option NodeId → List NodeId → List NodeId
  | [], _, L => L
  | (true, c) :: rest, _, L => placeL R rest (after c L) L
  | (false, c) :: rest, cur, L =>
    let ref := refOf R L cur
    if ref = some c then placeL R rest (after c L) L
    else placeL R rest ref (insertAt c ref (L.erase c))

/-- Anchored nodes of a placement list, in order. -/
def anch : List (Bool × NodeId) → List NodeId
  | [] => []
  | (true, c) :: rest => c :: anch rest
  | (false, _) :: rest => anch rest

def fR (S L : List NodeId) : List NodeId := L.filter (fun x => decide (x ∈ S))

theorem fR_append (S A B : List NodeId) : fR S (A ++ B) = fR S A ++ fR S B := by
  simp [fR, List.filter_append]

theorem fR_cons_mem (S L : List NodeId) (x : NodeId) (h : x ∈ S) : fR S (x :: L) = x :: fR S L := by
  simp [fR, List.filter_cons, h]

theorem fR_cons_not (S L : List NodeId) (x : NodeId) (h : x ∉ S) : fR S (x :: L) = fR S L := by
  simp [fR, List.filter_cons, h]

theorem mem_fR {S L : List NodeId} {x : NodeId} : x ∈ fR S L ↔ x ∈ L ∧ x ∈ S := by
  simp [fR]

/-! ### List facts -/

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

theorem fR_nil_of (S L : List NodeId) (h : ∀ x ∈ L, x ∉ S) : fR S L = [] := by
  simp only [fR, List.filter_eq_nil_iff, decide_eq_true_eq]; exact h

theorem fR_congr (S S' L : List NodeId) (h : ∀ x ∈ L, (x ∈ S ↔ x ∈ S')) : fR S L = fR S' L := by
  simp only [fR]; apply List.filter_congr; intro x hx; simp [h x hx]

theorem fR_erase (S A : List NodeId) (c : NodeId) (hc : c ∉ S) (hA : A.Nodup) :
    fR S (A.erase c) = fR S A := by
  rw [hA.erase_eq_filter]
  simp only [fR, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : x ∈ S
  · have : x ≠ c := fun e => hc (e ▸ hx)
    simp [hx, this]
  · simp [hx]

theorem fR_of_sublist (S O : List NodeId) (hs : S.Sublist O) (hO : O.Nodup) : fR S O = S := by
  induction hs with
  | slnil => rfl
  | @cons l₁ l₂ a hs ih =>
    rw [List.nodup_cons] at hO
    have : a ∉ l₁ := fun h => hO.1 (hs.subset h)
    rw [fR_cons_not _ _ _ this, ih hO.2]
  | @cons_cons l₁ l₂ a hs ih =>
    rw [List.nodup_cons] at hO
    rw [fR_cons_mem _ _ _ (by simp)]
    congr 1
    calc fR (a :: l₁) l₂ = fR l₁ l₂ := fR_congr _ _ _ (fun x hx => by
            constructor
            · intro h; rcases List.mem_cons.1 h with rfl | h; exact absurd hx hO.1; exact h
            · exact List.mem_cons_of_mem _)
      _ = l₁ := ih hO.2

/-- If the filtered list starts with `c` and `c` is not in `B1`, then nothing
of `B1` passes the filter. -/
theorem fR_split_head (S B1 B2 T : List NodeId) (c : NodeId) (hcS : c ∈ S) (hc : c ∉ B1)
    (h : fR S (B1 ++ c :: B2) = c :: T) : fR S B1 = [] ∧ fR S B2 = T := by
  rw [fR_append, fR_cons_mem _ _ _ hcS] at h
  cases h1 : fR S B1 with
  | nil => rw [h1] at h; simp at h; exact ⟨rfl, h⟩
  | cons y ys =>
    rw [h1] at h; simp only [List.cons_append, List.cons.injEq] at h
    have : y ∈ fR S B1 := by rw [h1]; simp
    exact absurd (h.1 ▸ (mem_fR.1 this).1) hc

theorem anch_sublist : ∀ (P : List (Bool × NodeId)) (O : List NodeId),
    (∀ (i : Nat) (c : NodeId), P[i]? = some (true, c) → O[i]? = some c) → (anch P).Sublist O
  | [], _, _ => List.nil_sublist _
  | (b, c) :: P, [], h => by
    cases b
    · have := anch_sublist P [] (fun i c' hi => by
        have := h (i + 1) c' (by simpa using hi); simp at this)
      simpa [anch] using this
    · have := h 0 c (by simp); simp at this
  | (b, c) :: P, o :: O, h => by
    have ih := anch_sublist P O (fun i c' hi => by
      have := h (i + 1) c' (by simpa using hi); simpa using this)
    cases b
    · simp only [anch]; exact ih.cons o
    · have := h 0 c (by simp); simp at this; subst this
      simp only [anch]; exact ih.cons_cons _

theorem anch_subset : ∀ (P : List (Bool × NodeId)), ∀ x ∈ anch P, x ∈ P.map (·.2)
  | [], _, h => by simp [anch] at h
  | (b, c) :: P, x, h => by
    cases b
    · simp only [anch] at h; simp [anch_subset P x h]
    · simp only [anch, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · simp [anch_subset P x h]

/-! ### The invariant -/

structure PInv (Q : List NodeId) (P : List (Bool × NodeId)) (L : List NodeId)
    (cur : Option NodeId) : Prop where
  nodup : L.Nodup
  split : ∃ A B, L = A ++ B ∧ cur = B.head? ∧ fR Q A = Q ∧ (∀ x ∈ B, x ∉ Q) ∧
    fR (anch P) B = anch P

/-- The cursor moves past `c`, the first placed node after it. -/
theorem pinv_skip (Q : List NodeId) (c : NodeId) (P : List (Bool × NodeId)) (L : List NodeId)
    (A B1 B2 : List NodeId) (hL : L = A ++ (B1 ++ c :: B2)) (hnd : L.Nodup)
    (hA : fR Q A = Q) (hB : ∀ x ∈ B1 ++ c :: B2, x ∉ Q)
    (hB2 : fR (anch P) B2 = anch P) :
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
  · rw [fR_append, fR_append]
    have h1 : fR (Q ++ [c]) A = Q := by
      calc fR (Q ++ [c]) A = fR Q A := fR_congr _ _ _ (fun x hx => by
              simp only [List.mem_append, List.mem_singleton]
              constructor
              · rintro (h | rfl); exact h; exact absurd hx hcA
              · exact Or.inl)
        _ = Q := hA
    have h2 : fR (Q ++ [c]) B1 = [] := fR_nil_of _ _ (fun x hx => by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hB x (by simp [hx]), fun e => hcB1 (e ▸ hx)⟩)
    rw [h1, h2, fR_cons_mem _ _ _ (by simp)]; simp [fR]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hB x (by simp [hx]), fun e => hcB2 (e ▸ hx)⟩

theorem placeL_inv : ∀ (P : List (Bool × NodeId)) (Q L : List NodeId) (cur : Option NodeId)
    (R : List NodeId), R = Q ++ P.map (·.2) → R.Nodup → PInv Q P L cur →
    fR R (placeL R P cur L) = R ∧ (placeL R P cur L).Nodup
  | [], Q, L, cur, R, hR, _, inv => by
    obtain ⟨A, B, hL, _, hA, hB, _⟩ := inv.split
    simp only [List.map_nil, List.append_nil] at hR; subst hR
    refine ⟨?_, inv.nodup⟩
    simp only [placeL]; rw [hL, fR_append, hA, fR_nil_of _ _ hB]; simp
  | (true, c) :: P, Q, L, cur, R, hR, hRnd, inv => by
    obtain ⟨A, B, hL, hcur, hA, hB, hanch⟩ := inv.split
    simp only [anch] at hanch
    have hcB : c ∈ B := by
      have : c ∈ fR (c :: anch P) B := by rw [hanch]; simp
      exact (mem_fR.1 this).1
    obtain ⟨B1, B2, hBs⟩ := List.append_of_mem hcB
    have hnd := inv.nodup
    have hcB1 : c ∉ B1 := by
      rw [hL, hBs] at hnd; intro h; rw [List.nodup_append, List.nodup_append] at hnd
      exact hnd.2.1.2.2 c h c (by simp) rfl
    have hcB2 : c ∉ B2 := by
      rw [hL, hBs] at hnd; intro h; rw [List.nodup_append, List.nodup_append, List.nodup_cons] at hnd
      exact hnd.2.1.2.1.1 h
    rw [hBs] at hanch
    obtain ⟨_, h2⟩ := fR_split_head _ B1 B2 _ c (by simp) hcB1 hanch
    have hB2 : fR (anch P) B2 = anch P := by
      calc fR (anch P) B2 = fR (c :: anch P) B2 := fR_congr _ _ _ (fun x hx => by
              have : x ≠ c := fun e => hcB2 (e ▸ hx)
              simp [this])
        _ = anch P := h2
    have inv' := pinv_skip Q c P L A B1 B2 (by rw [hL, hBs]) hnd hA (by rw [← hBs]; exact hB) hB2
    simp only [placeL]
    exact placeL_inv P (Q ++ [c]) L _ R (by subst hR; simp) hRnd inv'
  | (false, c) :: P, Q, L, cur, R, hR, hRnd, inv => by
    obtain ⟨A, B, hL, hcur, hA, hB, hanch⟩ := inv.split
    simp only [anch] at hanch
    have hnd := inv.nodup
    have hcR : c ∈ R := by rw [hR]; simp
    have hcQ : c ∉ Q := by
      rw [hR] at hRnd; simp only [List.map_cons] at hRnd
      rw [List.nodup_append] at hRnd
      intro h; exact hRnd.2.2 c h c (by simp) rfl
    have hcP : c ∉ P.map (·.2) := by
      rw [hR] at hRnd; simp only [List.map_cons] at hRnd
      rw [List.nodup_append, List.nodup_cons] at hRnd; exact hRnd.2.1.1
    have hcanch : c ∉ anch P := fun h => hcP (anch_subset P c h)
    have hanchR : ∀ x ∈ anch P, x ∈ R := fun x hx => by rw [hR]; simp [anch_subset P x hx]
    -- the reference node is the first placed node after the cursor
    have href : refOf R L cur = B.find? (· ∈ R) := by
      cases B with
      | nil => simp at hcur; subst hcur; simp [refOf]
      | cons o B' =>
        simp at hcur; subst hcur
        have hoA : o ∉ A := by
          rw [hL] at hnd; intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 o h o (by simp) rfl
        simp only [refOf]; rw [hL, dropWhile_split o A B' hoA]
    simp only [placeL]
    rw [href]
    split
    · -- c is already in place
      rename_i heq
      obtain ⟨_, as, bs, hBs, has⟩ := List.find?_eq_some_iff_append.1 heq
      have hasR : ∀ x ∈ as, x ∉ R := fun x hx => by simpa using has x hx
      have hcas : c ∉ as := fun h => hasR c h hcR
      rw [hBs] at hanch
      have hbs : fR (anch P) bs = anch P := by
        rw [fR_append, fR_nil_of _ _ (fun x hx h => hasR x hx (hanchR x h)),
          fR_cons_not _ _ _ hcanch] at hanch
        simpa using hanch
      have inv' := pinv_skip Q c P L A as bs (by rw [hL, hBs]) hnd hA (by rw [← hBs]; exact hB) hbs
      exact placeL_inv P (Q ++ [c]) L _ R (by subst hR; simp) hRnd inv'
    · rename_i hne
      apply placeL_inv P (Q ++ [c]) _ _ R (by subst hR; simp) hRnd
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
      have hAe : fR (Q ++ [c]) (A.erase c) = Q := by
        calc fR (Q ++ [c]) (A.erase c) = fR Q (A.erase c) := fR_congr _ _ _ (fun x hx => by
                simp only [List.mem_append, List.mem_singleton]
                constructor
                · rintro (h | rfl); exact h; exact absurd hx hcAe
                · exact Or.inl)
          _ = fR Q A := fR_erase Q A c hcQ hndA
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
        have hanchP : anch P = [] := by
          calc anch P = fR (anch P) B := hanch.symm
            _ = [] := fR_nil_of _ _ (fun x hx h => hBR x hx (hanchR x h))
        refine ⟨hL'nd, A.erase c ++ B ++ [c], [], ?_, rfl, ?_, by simp, by simp [hanchP, fR]⟩
        · rw [insertAt_none, hLe, List.erase_of_not_mem hcB]
          simp
        · rw [fR_append, fR_append, hAe,
            fR_nil_of _ _ (fun x hx h => hBR x hx (by
              rw [hR]; simp only [List.mem_append, List.mem_singleton] at h ⊢
              rcases h with h | h; exact Or.inl h; subst h; simp))]
          simp [fR]
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
        · rw [fR_append, fR_append, hAe,
            fR_nil_of _ _ (fun x hx h => hasR x hx (by
              rw [hR]; simp only [List.mem_append, List.mem_singleton] at h ⊢
              rcases h with h | h; exact Or.inl h; subst h; simp))]
          simp [fR]
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
          rw [fR_append, fR_nil_of _ _ (fun x hx h => hasR x hx (hanchR x h))] at hanch
          rw [List.nil_append] at hanch
          have hbsnd : bs.Nodup := by
            rw [hBs] at hndB; exact (List.nodup_cons.1 (List.nodup_append.1 hndB).2.1).2
          refine Eq.trans ?_ hanch
          by_cases hr : r ∈ anch P
          · rw [fR_cons_mem _ _ _ hr, fR_cons_mem _ _ _ hr, fR_erase _ bs c hcanch hbsnd]
          · rw [fR_cons_not _ _ _ hr, fR_cons_not _ _ _ hr, fR_erase _ bs c hcanch hbsnd]

/-- The placed nodes end up in the child list in placement order. -/
theorem placeL_correct (O : List NodeId) (P : List (Bool × NodeId)) (hO : O.Nodup)
    (hR : (P.map (·.2)).Nodup) (hanch : ∀ (i : Nat) (c : NodeId), P[i]? = some (true, c) → O[i]? = some c) :
    fR (P.map (·.2)) (placeL (P.map (·.2)) P O.head? O) = P.map (·.2) ∧
      (placeL (P.map (·.2)) P O.head? O).Nodup := by
  apply placeL_inv P [] O O.head? _ (by simp) hR
  exact ⟨hO, [], O, by simp, rfl, rfl, by simp, fR_of_sublist _ _ (anch_sublist P O hanch) hO⟩

end Snabbdom
