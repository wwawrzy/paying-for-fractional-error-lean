import Paper.Endpoints.Girth.HighGirthAttachmentPositionCount

/-! Finite ordered-position arithmetic used to bound the actual trimmed path. -/
namespace Paper.HighGirthFiniteGapSpan

theorem span_of_gaps (S : Finset Nat) : ∀ hS : S.Nonempty,
    (∀ i ∈ S, ∀ j ∈ S, i < j →
      (∀ k ∈ S, i < k → k < j → False) → j - i ≤ 5) →
    S.max' hS ≤ S.min' hS + 5 * (S.card - 1) := by
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
          (∀ k ∈ S, i < k → k < j → False) → j - i ≤ 5 := by
        intro i hi j hj hij hn
        apply hg i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
        intro k hk hik hkj
        rcases Finset.mem_insert.mp hk with rfl | hk
        · have hjlt := hmax j hj
          omega
        · exact hn k hk hik hkj
      have hstep : a - S.max' hS ≤ 5 := by
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

end Paper.HighGirthFiniteGapSpan

#print axioms Paper.HighGirthFiniteGapSpan.span_of_gaps
