/-
`placeWithFewestMoves` keeps the children at the indexes `longestIncreasingRun`
returns where they are and moves the others. That gives the right order when
the kept children are already children of the parent, in the order of their
new positions; the run is increasing in old position, which makes that so.
-/
import Snabbdom.Proofs.Children

namespace Snabbdom

theorem lisSearch_spec (seq : Nat → Int) (tails : Nat → Nat) (value : Int) (lo hi : Nat)
    (h : lo ≤ hi) :
    lisSearch seq tails value lo hi ≤ hi ∧ (lisSearch seq tails value lo hi = lo ∨
      seq (tails (lisSearch seq tails value lo hi - 1)) < value) := by
  induction lo, hi using lisSearch.induct seq tails value with
  | case1 lo hi hlt mid hv ih =>
    rw [lisSearch]; simp only [hlt, ite_true]; simp only [mid] at hv ih; simp only [hv, ite_true]
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨h1, Or.inr ?_⟩
    rcases h2 with h2 | h2
    · rw [h2, Nat.add_sub_cancel]; exact hv
    · exact h2
  | case2 lo hi hlt mid hv ih =>
    rw [lisSearch]; simp only [hlt, ite_true]; simp only [mid] at hv ih; simp only [hv, ite_false]
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact ⟨by omega, h2⟩
  | case3 lo hi hlt =>
    rw [lisSearch]; simp only [hlt, ite_false]
    exact ⟨h, Or.inl trivial⟩

def PrevOk (f : Nat → Int) (previous : Nat → Int) : Prop :=
  ∀ j, previous j = -1 ∨ (0 ≤ previous j ∧ (previous j).toNat < j ∧
    0 ≤ f (previous j).toNat ∧ f (previous j).toNat < f j)

structure LisInv (f : Nat → Int) (i : Nat) (s : LisState) : Prop where
  tails : ∀ m, m < s.length → s.tails m < i ∧ 0 ≤ f (s.tails m)
  prev : PrevOk f s.previous

theorem lisStep_inv (f : Nat → Int) (i : Nat) (s : LisState) (h : LisInv f i s) :
    LisInv f (i + 1) (lisStep f s i) := by
  unfold lisStep
  split
  · rename_i hfi
    obtain ⟨hlo, hlo'⟩ := lisSearch_spec f s.tails (f i) 0 s.length (Nat.zero_le _)
    generalize lisSearch f s.tails (f i) 0 s.length = lo at hlo hlo'
    constructor
    · intro m hm
      dsimp only at hm ⊢
      split
      · exact ⟨by omega, hfi⟩
      · rename_i hml
        have : m < s.length := by split at hm <;> omega
        have := h.tails m this; exact ⟨by omega, this.2⟩
    · intro j
      dsimp only
      split
      · rename_i hj
        subst hj
        split
        · rename_i hpos
          right
          have ht := h.tails (lo - 1) (by omega)
          rcases hlo' with e | hlt
          · omega
          · simp only [Int.toNat_natCast]
            exact ⟨by omega, ht.1, ht.2, hlt⟩
        · exact Or.inl rfl
      · exact h.prev j
  · exact ⟨fun m hm => by have := h.tails m hm; exact ⟨by omega, this.2⟩, h.prev⟩

theorem lis_fold_inv (f : Nat → Int) : ∀ n,
    LisInv f n ((List.range n).foldl (lisStep f) ⟨fun _ => 0, fun _ => -1, 0⟩)
  | 0 => ⟨fun m hm => absurd hm (Nat.not_lt_zero _), fun _ => Or.inl rfl⟩
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact lisStep_inv f n _ (lis_fold_inv f n)

theorem lisWalk_spec (f : Nat → Int) (previous : Nat → Int) (n : Nat) (hp : PrevOk f previous) :
    ∀ fuel k, (0 ≤ k → k.toNat < n ∧ 0 ≤ f k.toNat) →
      (∀ x ∈ lisWalk previous fuel k, 0 ≤ k ∧ x ≤ k.toNat ∧ f x ≤ f k.toNat ∧ x < n ∧ 0 ≤ f x) ∧
      (lisWalk previous fuel k).Pairwise (fun a b => b < a ∧ f b < f a)
  | 0, _, _ => by simp [lisWalk]
  | fuel + 1, k, hk => by
    unfold lisWalk
    split
    · rename_i hk0
      obtain ⟨hkn, hkf⟩ := hk hk0
      have hk' : 0 ≤ previous k.toNat → (previous k.toNat).toNat < n ∧ 0 ≤ f (previous k.toNat).toNat := by
        intro h0
        rcases hp k.toNat with e | ⟨_, h1, h2, _⟩
        · omega
        · exact ⟨by omega, h2⟩
      obtain ⟨ih1, ih2⟩ := lisWalk_spec f previous n hp fuel _ hk'
      have hlt : ∀ x ∈ lisWalk previous fuel (previous k.toNat), x < k.toNat ∧ f x < f k.toNat := by
        intro x hx
        obtain ⟨h0, hx1, hx2, _⟩ := ih1 x hx
        rcases hp k.toNat with e | ⟨_, h1, _, h3⟩
        · omega
        · exact ⟨by omega, by omega⟩
      refine ⟨?_, List.pairwise_cons.2 ⟨hlt, ih2⟩⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hk0, Nat.le_refl _, Int.le_refl _, hkn, hkf⟩
      · have := hlt x hx; have := ih1 x hx
        exact ⟨hk0, by omega, by omega, by omega, this.2.2.2.2⟩
    · simp

theorem pairwise_or {α} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l,
    a ≠ b → R a b ∨ R b a
  | [], _, _, ha, _, _, _ => by cases ha
  | x :: xs, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hb with eb | hb'
    · exact absurd (ea.trans eb.symm) hab
    · subst ea; exact Or.inl (h.1 b hb')
    · subst eb; exact Or.inr (h.1 a ha')
    · exact pairwise_or h.2 a ha' b hb' hab

theorem longestIncreasingRun_spec (seq : List Int) :
    (∀ i ∈ longestIncreasingRun seq, i < seq.length ∧ 0 ≤ seq.getD i (-1)) ∧
    ∀ a ∈ longestIncreasingRun seq, ∀ b ∈ longestIncreasingRun seq, a < b →
      seq.getD a (-1) < seq.getD b (-1) := by
  unfold longestIncreasingRun
  dsimp only
  have inv := lis_fold_inv (fun i => seq.getD i (-1)) seq.length
  generalize (List.range seq.length).foldl _ _ = s at inv
  have hk : ∀ k : Int, k = (if 0 < s.length then (s.tails (s.length - 1) : Int) else -1) →
      0 ≤ k → k.toNat < seq.length ∧ 0 ≤ seq.getD k.toNat (-1) := by
    intro k hk h0
    split at hk
    · subst hk; simp only [Int.toNat_natCast]; exact inv.tails _ (by omega)
    · omega
  obtain ⟨h1, h2⟩ := lisWalk_spec _ s.previous seq.length inv.prev seq.length _ (hk _ rfl)
  refine ⟨fun i hi => ⟨(h1 i hi).2.2.2.1, (h1 i hi).2.2.2.2⟩, ?_⟩
  intro a ha b hb hab
  rcases pairwise_or h2 a ha b hb (by omega) with h | h
  · omega
  · exact h.2

def insertAllList (next : Option NodeId) : List NodeId → List NodeId → List NodeId
  | [], L => L
  | n :: ns, L => insertAllList next ns (insertAt n next (L.erase n))

def placeFewestList : List (NodeId × Bool) → List NodeId → Option NodeId → List NodeId → List NodeId
  | [], blk, next, L => insertAllList next blk L
  | (n, true) :: rest, blk, next, L => placeFewestList rest [] (some n) (insertAllList next blk L)
  | (n, false) :: rest, blk, next, L => placeFewestList rest (n :: blk) next L

def stayOf (Z : List (NodeId × Bool)) : List NodeId := (Z.filter (·.2)).map (·.1)

theorem mem_stayOf {Z : List (NodeId × Bool)} {n : NodeId} : n ∈ stayOf Z ↔ (n, true) ∈ Z := by
  simp only [stayOf, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h, hb⟩, rfl⟩; simp only at hb; subst hb; exact h
  · intro h; exact ⟨(n, true), ⟨h, rfl⟩, rfl⟩

theorem insertAllList_mem (next : Option NodeId) : ∀ (blk L : List NodeId) (x : NodeId),
    x ∈ L → x ∈ insertAllList next blk L
  | [], _, _, h => h
  | n :: ns, L, x, h => by
    apply insertAllList_mem next ns
    rw [mem_insertAt]
    by_cases hx : x = n
    · exact Or.inl hx
    · exact Or.inr ((List.mem_erase_of_ne hx).2 h)

theorem insertAllList_sub (next : Option NodeId) : ∀ (blk L : List NodeId) (x : NodeId),
    x ∈ insertAllList next blk L → x ∈ L ∨ x ∈ blk
  | [], _, _, h => Or.inl h
  | n :: ns, L, x, h => by
    rcases insertAllList_sub next ns _ x h with h | h
    · rw [mem_insertAt] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl (List.mem_of_mem_erase h)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem insertAllList_nodup (next : Option NodeId) : ∀ (blk L : List NodeId),
    L.Nodup → (insertAllList next blk L).Nodup
  | [], _, h => h
  | n :: ns, _, h => insertAllList_nodup next ns _ (nodup_insertAt _ _ _ (h.erase n) h.not_mem_erase)

theorem placeFewestList_mem : ∀ (rest : List (NodeId × Bool)) (blk : List NodeId) (next : Option NodeId)
    (L : List NodeId) (x : NodeId), x ∈ L → x ∈ placeFewestList rest blk next L
  | [], blk, next, L, x, h => insertAllList_mem next blk L x h
  | (_, true) :: rest, blk, next, L, x, h =>
    placeFewestList_mem rest [] _ _ x (insertAllList_mem next blk L x h)
  | (_, false) :: rest, _, next, L, x, h => placeFewestList_mem rest _ next L x h

theorem placeFewestList_sub : ∀ (rest : List (NodeId × Bool)) (blk : List NodeId) (next : Option NodeId)
    (L : List NodeId) (x : NodeId), x ∈ placeFewestList rest blk next L →
    x ∈ L ∨ x ∈ blk ∨ x ∈ rest.map (·.1)
  | [], blk, next, L, x, h => by
    rcases insertAllList_sub next blk L x h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | (n, true) :: rest, blk, next, L, x, h => by
    rcases placeFewestList_sub rest [] _ _ x h with h | h | h
    · rcases insertAllList_sub next blk L x h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · cases h
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))
  | (n, false) :: rest, blk, next, L, x, h => by
    rcases placeFewestList_sub rest _ next L x h with h | h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

theorem append_cons_cancel (r : NodeId) : ∀ (X Y A B : List NodeId), X ++ r :: Y = A ++ r :: B →
    r ∉ X → r ∉ A → X = A ∧ Y = B
  | [], Y, [], B, h, _, _ => by simpa using h
  | [], Y, a :: A, B, h, _, hA => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hA
  | x :: X, Y, [], B, h, hX, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hX
  | x :: X, Y, a :: A, B, h, hX, hA => by
    simp only [List.cons_append, List.cons.injEq] at h
    simp only [List.mem_cons, not_or] at hX hA
    obtain ⟨e1, e2⟩ := append_cons_cancel r X Y A B h.2 hX.2 hA.2
    exact ⟨by rw [h.1, e1], e2⟩

theorem keepIn_insert (U L A S : List NodeId) (b : NodeId) (next : Option NodeId) (hL : L.Nodup)
    (hb : b ∉ U) (h : keepIn U L = A ++ S) (hn : next = S.head?) (hS : ∀ x ∈ S, x ∈ U) :
    keepIn (U ++ [b]) (insertAt b next (L.erase b)) = A ++ [b] ++ S := by
  have hM := hL.erase b
  have hbM : b ∉ L.erase b := hL.not_mem_erase
  have hkM : keepIn U (L.erase b) = A ++ S := by rw [keepIn_erase U L b hb hL, h]
  have hU : ∀ X : List NodeId, b ∉ X → keepIn (U ++ [b]) X = keepIn U X := fun X hX =>
    keepIn_congr _ _ _ (fun x hx => by
      have : x ≠ b := fun e => hX (e ▸ hx)
      simp [this])
  cases S with
  | nil =>
    subst hn
    rw [List.head?_nil, insertAt_none, keepIn_append, hU _ hbM, hkM, keepIn_cons_mem _ _ _ (by simp)]
    simp [keepIn]
  | cons r B =>
    subst hn
    rw [List.head?_cons]
    have hrU : r ∈ U := hS r List.mem_cons_self
    have hrM : r ∈ L.erase b := (mem_keepIn.1 (by rw [hkM]; simp : r ∈ keepIn U (L.erase b))).1
    obtain ⟨X, Y, hXY⟩ := List.append_of_mem hrM
    have hrX : r ∉ X := by
      rw [hXY, List.nodup_append] at hM; exact fun hx => hM.2.2 r hx r List.mem_cons_self rfl
    have hbX : b ∉ X := fun hx => hbM (by rw [hXY]; simp [hx])
    have hbY : b ∉ Y := fun hy => hbM (by rw [hXY]; simp [hy])
    have hrb : r ≠ b := fun e => hb (e ▸ hrU)
    rw [hXY, insertAt_split b r X Y hrX]
    rw [hXY, keepIn_append, keepIn_cons_mem _ _ _ hrU] at hkM
    have hnd : (A ++ r :: B).Nodup := by
      rw [← h]; exact hL.sublist List.filter_sublist
    have hrA : r ∉ A := by
      rw [List.nodup_append] at hnd; exact fun ha => hnd.2.2 r ha r List.mem_cons_self rfl
    obtain ⟨e1, e2⟩ := append_cons_cancel r _ _ A B hkM (fun hx => hrX (mem_keepIn.1 hx).1) hrA
    rw [keepIn_append, hU X hbX, e1, keepIn_cons_mem _ _ _ (by simp),
      keepIn_cons_mem _ _ _ (by simp [hrU]), hU Y hbY, e2]
    simp

theorem insertAllList_keep (next : Option NodeId) : ∀ (blk U L A S : List NodeId),
    L.Nodup → blk.Nodup → (∀ b ∈ blk, b ∉ U) → keepIn U L = A ++ S → next = S.head? →
    (∀ x ∈ S, x ∈ U) → keepIn (U ++ blk) (insertAllList next blk L) = A ++ blk ++ S
  | [], U, L, A, S, _, _, _, h, _, _ => by simpa [insertAllList] using h
  | b :: blk, U, L, A, S, hL, hnd, hU, h, hn, hS => by
    rw [List.nodup_cons] at hnd
    have h1 := keepIn_insert U L A S b next hL (hU b List.mem_cons_self) h hn hS
    have ih := insertAllList_keep next blk (U ++ [b]) _ (A ++ [b]) S
      (nodup_insertAt _ _ _ (hL.erase b) hL.not_mem_erase) hnd.2
      (fun b' hb' => by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hU b' (List.mem_cons_of_mem _ hb'), fun e => hnd.1 (e ▸ hb')⟩)
      h1 hn (fun x hx => List.mem_append_left _ (hS x hx))
    simp only [insertAllList]
    simpa using ih

theorem nodup_fst_inj : ∀ {Z : List (NodeId × Bool)}, (Z.map (·.1)).Nodup → ∀ {a b}, a ∈ Z → b ∈ Z →
    a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | z :: Z, h, a, b, ha, hb, e => by
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem hb') h.1
    · exact absurd (e.symm ▸ List.mem_map_of_mem ha') h.1
    · exact nodup_fst_inj h.2 ha' hb' e

theorem placeFewestList_keep (Z : List (NodeId × Bool)) (hZ : (Z.map (·.1)).Nodup) :
    ∀ (rest Zs : List (NodeId × Bool)) (blk S : List NodeId) (next : Option NodeId) (L : List NodeId),
    Z = rest.reverse ++ Zs → Zs.map (·.1) = blk ++ S → (∀ b ∈ blk, b ∉ stayOf Z) →
    next = S.head? → keepIn (stayOf Z ++ S) L = stayOf rest.reverse ++ S → L.Nodup →
    keepIn (Z.map (·.1)) (placeFewestList rest blk next L) = Z.map (·.1)
  | [], Zs, blk, S, next, L, hz, hbS, hblk, hn, hk, hL => by
    simp only [List.reverse_nil, List.nil_append] at hz
    rw [← hz] at hbS
    have hnd : (blk ++ S).Nodup := hbS ▸ hZ
    have := insertAllList_keep next blk (stayOf Z ++ S) L [] S hL (List.nodup_append.1 hnd).1
      (fun b hb => by
        simp only [List.mem_append, not_or]
        exact ⟨hblk b hb, fun hs => (List.nodup_append.1 hnd).2.2 b hb b hs rfl⟩)
      (by simpa [stayOf] using hk) hn (fun x hx => List.mem_append_right _ hx)
    simp only [placeFewestList]
    rw [hbS]
    refine Eq.trans (keepIn_congr _ _ _ (fun x _ => ?_)) (this.trans (by simp))
    simp only [List.mem_append]
    constructor
    · rintro (h | h) <;> simp [h]
    · rintro ((h | h) | h)
      · have hm : x ∈ Z.map (·.1) := by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (by simpa [stayOf] using h : x ∈ (Z.filter (·.2)).map (·.1))
          exact List.mem_map_of_mem ((List.mem_filter.1 hp).1)
        rw [hbS] at hm; exact List.mem_append.1 hm
      · exact Or.inr h
      · exact Or.inl h
  | (n, false) :: rest, Zs, blk, S, next, L, hz, hbS, hblk, hn, hk, hL => by
    simp only [placeFewestList]
    have hnZ : (n, false) ∈ Z := by rw [hz]; simp
    refine placeFewestList_keep Z hZ rest ((n, false) :: Zs) (n :: blk) S next L
      (by rw [hz]; simp) (by simp [hbS]) ?_ hn (by rw [hk]; simp [stayOf]) hL
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · intro hs
      have := nodup_fst_inj hZ hnZ (mem_stayOf.1 hs) rfl
      simp at this
    · exact hblk b hb
  | (n, true) :: rest, Zs, blk, S, next, L, hz, hbS, hblk, hn, hk, hL => by
    simp only [placeFewestList]
    have hnZ : n ∈ stayOf Z := mem_stayOf.2 (by rw [hz]; simp)
    have hnd : (n :: (blk ++ S)).Nodup := by
      have := hZ; rw [hz] at this; simp only [List.map_append, List.map_reverse] at this
      rw [List.nodup_append] at this
      have h2 := this.2.1; rw [hbS] at h2
      refine List.nodup_cons.2 ⟨fun hm => ?_, h2⟩
      exact this.2.2 n (by simp) n (by rw [hbS]; exact hm) rfl
    rw [List.nodup_cons] at hnd
    have hfl := insertAllList_keep next blk (stayOf Z ++ S) L (stayOf rest.reverse ++ [n]) S hL
      (List.nodup_append.1 hnd.2).1
      (fun b hb => by
        simp only [List.mem_append, not_or]
        exact ⟨hblk b hb, fun hs => (List.nodup_append.1 hnd.2).2.2 b hb b hs rfl⟩)
      (by rw [hk]; simp [stayOf]) hn (fun x hx => List.mem_append_right _ hx)
    refine placeFewestList_keep Z hZ rest ((n, true) :: Zs) [] (n :: (blk ++ S)) (some n) _
      (by rw [hz]; simp) (by simp [hbS]) (by simp) rfl ?_ (insertAllList_nodup next blk L hL)
    refine Eq.trans (keepIn_congr _ (stayOf Z ++ S ++ blk) _ (fun x _ => ?_)) (hfl.trans (by simp))
    by_cases hx : x = n
    · subst hx; simp [hnZ]
    · simp only [List.mem_append, List.mem_cons, hx, false_or]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro ((h | h) | h) <;> simp [h]

theorem placeFewestList_correct (Z : List (NodeId × Bool)) (L : List NodeId)
    (hZ : (Z.map (·.1)).Nodup) (hL : L.Nodup) (hstay : keepIn (stayOf Z) L = stayOf Z) :
    keepIn (Z.map (·.1)) (placeFewestList Z.reverse [] none L) = Z.map (·.1) :=
  placeFewestList_keep Z hZ Z.reverse [] [] [] none L (by simp) rfl (by simp) rfl
    (by simpa using hstay) hL

theorem insertAllBefore_spec (elm : NodeId) (next : Option NodeId) : ∀ (blk : List NodeId) (d : Dom)
    (ex : DomNode), HeapWF d → d.nodes elm = some ex → blk.Nodup →
    (∀ b ∈ blk, b ≠ elm ∧ ∃ x, d.nodes b = some x ∧ (x.parent = none ∨ x.parent = some elm)) →
    (∀ r, next = some r → r ∈ ex.children ∧ r ∉ blk) →
    HeapWF (insertAllBefore elm next blk d) ∧ (insertAllBefore elm next blk d).ok = d.ok ∧
    (insertAllBefore elm next blk d).next = d.next ∧
    (insertAllBefore elm next blk d).nodes elm =
      some { ex with children := insertAllList next blk ex.children } ∧
    (∀ m, m ≠ elm → SameContent d (insertAllBefore elm next blk d) m) ∧
    (∀ m, m ≠ elm → m ∉ blk → (insertAllBefore elm next blk d).nodes m = d.nodes m)
  | [], d, ex, hw, he, _, _, _ => by
    exact ⟨hw, rfl, rfl, by simp [insertAllBefore, insertAllList, he], fun m _ => SameContent.of_eq rfl,
      fun _ _ _ => rfl⟩
  | b :: blk, d, ex, hw, he, hnd, hb, hnext => by
    obtain ⟨hbe, bx, hbx, hpar⟩ := hb b List.mem_cons_self
    rw [List.nodup_cons] at hnd
    have hi : Dom.InsertOk (d.log (.insertBefore elm b next)) elm b next ex bx :=
      ⟨he, hbx, hbe, hpar, fun r hr => ⟨(hnext r hr).1, fun e => (hnext r hr).2 (e ▸ List.mem_cons_self)⟩⟩
    have hwl := Dom.log_wf (.insertBefore elm b next) hw
    have hN := Dom.preInsert_nodes hwl hi
    let d1 := d.insertBefore elm b next
    have hd1 : d1 = (d.log (.insertBefore elm b next)).preInsert elm b next := rfl
    have w1 : HeapWF d1 := hd1 ▸ Dom.preInsert_wf hwl hi
    have he1 : d1.nodes elm = some { ex with children := insertAt b next (ex.children.erase b) } := by
      rw [hd1, hN]; simp
    have hb1 : ∀ b' ∈ blk, b' ≠ elm ∧ ∃ x, d1.nodes b' = some x ∧
        (x.parent = none ∨ x.parent = some elm) := by
      intro b' hb'
      obtain ⟨h1, x, hx, hxp⟩ := hb b' (List.mem_cons_of_mem _ hb')
      have : b' ≠ b := fun e => hnd.1 (e ▸ hb')
      exact ⟨h1, x, by rw [hd1, hN]; simp [h1, this, hx], hxp⟩
    have hnext1 : ∀ r, next = some r → r ∈ insertAt b next (ex.children.erase b) ∧ r ∉ blk := by
      intro r hr
      obtain ⟨h1, h2⟩ := hnext r hr
      simp only [List.mem_cons, not_or] at h2
      exact ⟨(mem_insertAt _ _ _ _).2 (Or.inr ((List.mem_erase_of_ne h2.1).2 h1)), h2.2⟩
    obtain ⟨w, ok, nx, ne, sc, fr⟩ := insertAllBefore_spec elm next blk d1 _ w1 he1 hnd.2 hb1 hnext1
    simp only [insertAllBefore, insertAllList]
    refine ⟨w, ?_, ?_, ne, ?_, ?_⟩
    · rw [ok, hd1, Dom.preInsert_ok hi]; rfl
    · rw [nx, hd1]; simp
    · intro m hm
      refine SameContent.trans ?_ (sc m hm)
      unfold SameContent
      rw [hd1, hN, ite_eq_right hm]
      split
      · rename_i h; subst h; simp [hbx, DomNode.content]
      · rfl
    · intro m hm hm'
      simp only [List.mem_cons, not_or] at hm'
      rw [fr m hm hm'.2, hd1, hN, ite_eq_right hm, ite_eq_right hm'.1]; rfl

theorem placeFewest_spec (elm : NodeId) : ∀ (rest : List (NodeId × Bool)) (blk : List NodeId)
    (next : Option NodeId) (d : Dom) (ex : DomNode), HeapWF d → d.nodes elm = some ex →
    (blk ++ rest.map (·.1)).Nodup →
    (∀ b ∈ blk ++ rest.map (·.1), b ≠ elm ∧ ∃ x, d.nodes b = some x ∧
      (x.parent = none ∨ x.parent = some elm)) →
    (∀ r, next = some r → r ∈ ex.children ∧ r ∉ blk ++ rest.map (·.1)) →
    (∀ n, (n, true) ∈ rest → n ∈ ex.children) →
    HeapWF (placeFewest elm rest blk next d) ∧ (placeFewest elm rest blk next d).ok = d.ok ∧
    (placeFewest elm rest blk next d).next = d.next ∧
    (placeFewest elm rest blk next d).nodes elm =
      some { ex with children := placeFewestList rest blk next ex.children } ∧
    (∀ m, m ≠ elm → SameContent d (placeFewest elm rest blk next d) m) ∧
    (∀ m, m ≠ elm → m ∉ blk ++ rest.map (·.1) → (placeFewest elm rest blk next d).nodes m = d.nodes m)
  | [], blk, next, d, ex, hw, he, hnd, hb, hnext, _ => by
    simp only [List.map_nil, List.append_nil] at hnd hb hnext ⊢
    exact insertAllBefore_spec elm next blk d ex hw he hnd hb hnext
  | (n, true) :: rest, blk, next, d, ex, hw, he, hnd, hb, hnext, hstay => by
    simp only [List.map_cons] at hnd hb hnext ⊢
    have hnd' := (List.perm_middle.nodup_iff).1 hnd
    rw [List.nodup_cons, List.nodup_append] at hnd'
    obtain ⟨w1, ok1, nx1, ne1, sc1, fr1⟩ := insertAllBefore_spec elm next blk d ex hw he hnd'.2.1
      (fun b hb' => hb b (List.mem_append_left _ hb'))
      (fun r hr => ⟨(hnext r hr).1, fun h => (hnext r hr).2 (List.mem_append_left _ h)⟩)
    have hnotblk : ∀ b ∈ rest.map (·.1), b ∉ blk := fun b hb' hb'' => hnd'.2.2.2 b hb'' b hb' rfl
    have hstay' : ∀ n', (n', true) ∈ rest → n' ∈ insertAllList next blk ex.children :=
      fun n' h => insertAllList_mem next blk _ n' (hstay n' (List.mem_cons_of_mem _ h))
    obtain ⟨w, ok, nx, ne, sc, fr⟩ := placeFewest_spec elm rest [] (some n) _ _ w1 ne1
      (by simpa using hnd'.2.2.1)
      (fun b hb' => by
        simp only [List.nil_append] at hb'
        obtain ⟨h1, x, hx, hxp⟩ := hb b (by simp [hb'])
        exact ⟨h1, x, by rw [fr1 b h1 (hnotblk b hb')]; exact hx, hxp⟩)
      (fun r hr => by
        cases hr
        exact ⟨insertAllList_mem next blk _ _ (hstay _ List.mem_cons_self), by simpa using fun h => hnd'.1 (List.mem_append_right _ h)⟩)
      hstay'
    simp only [placeFewest, placeFewestList]
    refine ⟨w, by rw [ok, ok1], by rw [nx, nx1], ne, fun m hm => (sc1 m hm).trans (sc m hm), ?_⟩
    intro m hm hm'
    simp only [List.mem_append, List.mem_cons, not_or] at hm'
    rw [fr m hm (by simpa using hm'.2.2), fr1 m hm hm'.1]
  | (n, false) :: rest, blk, next, d, ex, hw, he, hnd, hb, hnext, hstay => by
    simp only [List.map_cons] at hnd hb hnext ⊢
    have hmem : ∀ b, b ∈ (n :: blk) ++ rest.map (·.1) ↔ b ∈ blk ++ n :: rest.map (·.1) := by
      intro b; simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    obtain ⟨w, ok, nx, ne, sc, fr⟩ := placeFewest_spec elm rest (n :: blk) next d ex hw he
      (by rw [List.cons_append]; exact List.perm_middle.nodup_iff.1 hnd)
      (fun b h => hb b ((hmem b).1 h))
      (fun r hr => ⟨(hnext r hr).1, fun h => (hnext r hr).2 ((hmem r).1 h)⟩)
      (fun n' h => hstay n' (List.mem_cons_of_mem _ h))
    simp only [placeFewest, placeFewestList]
    exact ⟨w, ok, nx, ne, sc, fun m hm hm' => fr m hm (fun h => hm' ((hmem m).1 h))⟩

theorem sublist_of_pos : ∀ (L : List NodeId) (f : NodeId → Nat), (∀ j (h : j < L.length), f L[j] = j) →
    ∀ S : List NodeId, (∀ x ∈ S, x ∈ L) → S.Pairwise (fun a b => f a < f b) → S.Sublist L
  | [], _, _, S, hS, _ => by
    cases S with
    | nil => exact List.Sublist.slnil
    | cons x _ => exact absurd (hS x List.mem_cons_self) List.not_mem_nil
  | y :: L, f, hf, S, hS, hp => by
    have hy : f y = 0 := hf 0 (by simp)
    have hrest : ∀ z ∈ y :: L, z ≠ y → z ∈ L ∧ 1 ≤ f z := by
      intro z hz hzy
      have hzL : z ∈ L := by simpa [hzy] using hz
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hzL
      have := hf (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      exact ⟨hzL, by omega⟩
    have hf' : ∀ j (h : j < L.length), (fun x => f x - 1) L[j] = j := by
      intro j hj
      have := hf (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      dsimp only; omega
    have sub : ∀ T : List NodeId, (∀ x ∈ T, x ∈ y :: L ∧ x ≠ y) →
        T.Pairwise (fun a b => f a < f b) → T.Sublist L := by
      intro T hT hTp
      apply sublist_of_pos L (fun x => f x - 1) hf' T (fun x hx => (hrest x (hT x hx).1 (hT x hx).2).1)
      refine hTp.imp_of_mem (fun {a b} ha _ hab => ?_)
      have := (hrest a (hT a ha).1 (hT a ha).2).2
      omega
    cases S with
    | nil => exact List.nil_sublist _
    | cons x S =>
      rw [List.pairwise_cons] at hp
      have hS' : ∀ z ∈ S, z ∈ y :: L ∧ z ≠ y := by
        intro z hz
        refine ⟨hS z (List.mem_cons_of_mem _ hz), fun e => ?_⟩
        have := hp.1 z hz; rw [e, hy] at this; omega
      by_cases hxy : x = y
      · subst hxy; exact (sub S hS' hp.2).cons_cons _
      · refine (sub (x :: S) ?_ (List.pairwise_cons.2 hp)).cons _
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨hS z List.mem_cons_self, hxy⟩
        · exact hS' z hz

/-- `hidx` is what `oldIndexOf` provides: each non-negative entry of `oldIndex`
is the position in `ex.children` of that node of `R`. It makes the nodes at the
indexes of `longestIncreasingRun` already ordered in `ex.children`, so moving
only the others puts all of `R` in order. -/
theorem placeWithFewestMoves_spec (elm : NodeId) (R : List NodeId) (oldIndex : List Int) (d : Dom)
    (ex : DomNode) (hw : HeapWF d) (he : d.nodes elm = some ex) (hLnd : ex.children.Nodup)
    (hR : R.Nodup)
    (hRe : ∀ x ∈ R, x ≠ elm ∧ ∃ y, d.nodes x = some y ∧ (y.parent = none ∨ y.parent = some elm))
    (hidx : ∀ i (hi : i < R.length), 0 ≤ oldIndex.getD i (-1) →
      ∃ j, ∃ hj : j < ex.children.length, oldIndex.getD i (-1) = j ∧ ex.children[j] = R[i]) :
    HeapWF (placeWithFewestMoves elm R oldIndex d) ∧
    (placeWithFewestMoves elm R oldIndex d).ok = d.ok ∧
    (placeWithFewestMoves elm R oldIndex d).next = d.next ∧
    ∃ L', (placeWithFewestMoves elm R oldIndex d).nodes elm = some { ex with children := L' } ∧
      keepIn R L' = R ∧ (∀ x ∈ L', x ∈ ex.children ∨ x ∈ R) ∧ (∀ x ∈ ex.children, x ∈ L') ∧
      (∀ m, m ≠ elm → SameContent d (placeWithFewestMoves elm R oldIndex d) m) ∧
      (∀ m, m ≠ elm → m ∉ R → (placeWithFewestMoves elm R oldIndex d).nodes m = d.nodes m) := by
  have hrs := longestIncreasingRun_spec oldIndex
  unfold placeWithFewestMoves
  dsimp only
  generalize longestIncreasingRun oldIndex = run at hrs ⊢
  generalize hZ : R.zip ((List.range R.length).map fun i => decide (i ∈ run)) = Z
  have hZfst : Z.map (·.1) = R := by rw [← hZ]; exact List.map_fst_zip (by simp)
  have hZlen : Z.length = R.length := by rw [← hZ]; simp
  have hZget : ∀ i (h : i < Z.length), Z[i] = (R[i]'(hZlen ▸ h), decide (i ∈ run)) := by
    intro i h; subst hZ; simp [List.getElem_zip]
  let L := ex.children
  let f : NodeId → Nat := fun x => (L.findIdx? (fun y => decide (y = x))).getD 0
  have hf : ∀ j (h : j < L.length), f L[j] = j := by
    intro j hj
    have : L.findIdx? (fun y => decide (y = L[j])) = some j := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨hj, by simp, fun j' hj' hp => ?_⟩
      have e : L[j'] = L[j] := by simpa using hp
      have := idx_inj L j' j L[j] hLnd (by rw [List.getElem?_eq_getElem (by omega), e])
        (List.getElem?_eq_getElem hj)
      omega
    simp only [f, this, Option.getD_some]
  have hpos : ∀ i (hi : i < R.length), i ∈ run →
      ∃ j, ∃ hj : j < L.length, oldIndex.getD i (-1) = j ∧ L[j] = R[i] ∧ f R[i] = j := by
    intro i hi hir
    obtain ⟨j, hj, e1, e2⟩ := hidx i hi (hrs.1 i hir).2
    exact ⟨j, hj, e1, e2, by rw [← e2]; exact hf j hj⟩
  have hmem : ∀ x ∈ stayOf Z, ∃ i, ∃ hi : i < R.length, i ∈ run ∧ R[i] = x := by
    intro x hx
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 (mem_stayOf.1 hx)
    rw [hZget i hi] at e
    simp only [Prod.mk.injEq, decide_eq_true_eq] at e
    exact ⟨i, hZlen ▸ hi, e.2, e.1⟩
  have hstayL : ∀ x ∈ stayOf Z, x ∈ L := by
    intro x hx
    obtain ⟨i, hi, hir, rfl⟩ := hmem x hx
    obtain ⟨j, hj, _, e, _⟩ := hpos i hi hir
    rw [← e]; exact List.getElem_mem hj
  have hsorted : (stayOf Z).Pairwise (fun a b => f a < f b) := by
    unfold stayOf
    rw [List.pairwise_map, List.pairwise_filter, List.pairwise_iff_getElem]
    intro i i' hi hi' hlt h1 h2
    rw [hZget i hi] at h1 ⊢; rw [hZget i' hi'] at h2 ⊢
    simp only [decide_eq_true_eq] at h1 h2
    obtain ⟨j, hj, e1, _, f1⟩ := hpos i (hZlen ▸ hi) h1
    obtain ⟨j', hj', e1', _, f1'⟩ := hpos i' (hZlen ▸ hi') h2
    have := hrs.2 i h1 i' h2 hlt
    rw [e1, e1'] at this
    dsimp only; rw [f1, f1']; omega
  have hstay : keepIn (stayOf Z) L = stayOf Z :=
    keepIn_of_sublist _ _ (sublist_of_pos L f hf _ hstayL hsorted) hLnd
  have hZnd : (Z.map (·.1)).Nodup := hZfst ▸ hR
  have hrev : Z.reverse.map (·.1) = R.reverse := by rw [List.map_reverse, hZfst]
  have hmemR : ∀ x, x ∈ [] ++ Z.reverse.map (·.1) ↔ x ∈ R := by
    intro x; rw [List.nil_append, hrev, List.mem_reverse]
  obtain ⟨w, ok, nx, ne, sc, fr⟩ := placeFewest_spec elm Z.reverse [] none d ex hw he
    (by rw [List.nil_append, hrev]; exact List.pairwise_reverse.2 (hR.imp Ne.symm))
    (fun b hb => hRe b ((hmemR b).1 hb)) (fun r hr => by cases hr)
    (fun n hn => hstayL n (mem_stayOf.2 (List.mem_reverse.1 hn)))
  refine ⟨w, ok, nx, _, ne, ?_, ?_, fun x hx => placeFewestList_mem _ _ _ _ x hx, sc,
    fun m hm hmR => fr m hm (fun h => hmR ((hmemR m).1 h))⟩
  · have := placeFewestList_correct Z L hZnd hLnd hstay
    rwa [hZfst] at this
  · intro x hx
    rcases placeFewestList_sub _ _ _ _ x hx with h | h | h
    · exact Or.inl h
    · cases h
    · rw [hrev, List.mem_reverse] at h; exact Or.inr h

end Snabbdom
