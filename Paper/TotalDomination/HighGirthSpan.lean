import Paper.TotalDomination.HighGirthBadPaths

namespace Paper.TotalDomination.HighGirthSpan

theorem span_of_gaps (S : Finset Nat) : ∀ hS : S.Nonempty,
    (∀ i ∈ S, ∀ j ∈ S, i < j →
      (∀ k ∈ S, i < k → k < j → False) → j - i ≤ 7) →
    S.max' hS ≤ S.min' hS + 7 * (S.card - 1) := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro hs
    simp at hs
  | insert a S hmax ih =>
    intro hs hg
    by_cases hS : S.Nonempty
    · have hne : a ∉ S := fun ha => (hmax a ha).false
      have hlt : S.max' hS < a := hmax _ (Finset.max'_mem S hS)
      have hmina : S.min' hS < a := hmax _ (Finset.min'_mem S hS)
      have hgs : ∀ i ∈ S, ∀ j ∈ S, i < j →
          (∀ k ∈ S, i < k → k < j → False) → j - i ≤ 7 := by
        intro i hi j hj hij hn
        apply hg i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
        intro k hk hik hkj
        rcases Finset.mem_insert.mp hk with rfl | hk
        · have hjlt := hmax j hj
          omega
        · exact hn k hk hik hkj
      have hstep : a - S.max' hS ≤ 7 := by
        apply hg (S.max' hS) (Finset.mem_insert_of_mem (Finset.max'_mem S hS)) a (Finset.mem_insert_self _ _) hlt
        intro k hk hmk hka
        rcases Finset.mem_insert.mp hk with rfl | hk
        · omega
        · have hkmax := Finset.le_max' S k hk
          omega
      have hb := ih hS hgs
      have hpos : 0 < S.card := Finset.card_pos.mpr hS
      rw [Finset.max'_insert a S hS,Finset.min'_insert a S hS,
        max_eq_left hlt.le,min_eq_right hmina.le,Finset.card_insert_of_notMem hne]
      omega
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp

theorem span_of_short_first_gap (S : Finset ℕ) (hS : S.Nonempty) (hcard : 2 ≤ S.card)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j →
      (∀ k ∈ S, i < k → k < j → False) → j-i ≤ 7)
    (hfirst : ∀ j ∈ S, S.min' hS < j →
      (∀ k ∈ S, S.min' hS < k → k < j → False) → j-S.min' hS ≤ 5) :
    S.max' hS ≤ S.min' hS+5+7*(S.card-2) := by
  let m := S.min' hS
  let T := S.erase m
  have hmS : m ∈ S := Finset.min'_mem S hS
  have hTc : T.card+1 = S.card := Finset.card_erase_add_one hmS
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hminT : T.min' hT ∈ T := Finset.min'_mem T hT
  have hmT : m < T.min' hT := by
    have hh := Finset.min'_le S _ (Finset.mem_erase.mp hminT).2
    have hn := (Finset.mem_erase.mp hminT).1
    dsimp only [m] at *
    omega
  have hminmax : m < S.max' hS := hmT.trans_le (Finset.le_max' S _ (Finset.mem_erase.mp hminT).2)
  have hmaxT : T.max' hT = S.max' hS := by
    apply le_antisymm
    · exact Finset.le_max' S _ (Finset.mem_erase.mp (Finset.max'_mem T hT)).2
    · apply Finset.le_max' T
      exact Finset.mem_erase.mpr ⟨by omega,Finset.max'_mem S hS⟩
  have hgapT : ∀ i ∈ T, ∀ j ∈ T, i < j →
      (∀ k ∈ T, i < k → k < j → False) → j-i ≤ 7 := by
    intro i hi j hj hij hn
    apply hgap i (Finset.mem_erase.mp hi).2 j (Finset.mem_erase.mp hj).2 hij
    intro k hk hik hkj
    have hmi := Finset.min'_le S i (Finset.mem_erase.mp hi).2
    apply hn k (Finset.mem_erase.mpr ⟨by dsimp only [m] at *; omega,hk⟩) hik hkj
  have hspan := span_of_gaps T hT hgapT
  rw [hmaxT] at hspan
  have hstep : T.min' hT-m ≤ 5 := by
    apply hfirst (T.min' hT) (Finset.mem_erase.mp hminT).2 hmT
    intro k hk hmk hkn
    have hkT : k ∈ T := Finset.mem_erase.mpr ⟨by omega,hk⟩
    have hh := Finset.min'_le T k hkT
    omega
  dsimp only [m] at *
  omega

end Paper.TotalDomination.HighGirthSpan
