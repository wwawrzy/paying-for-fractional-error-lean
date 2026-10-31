import Paper.Endpoints.Girth.HighGirthSlack
set_option maxHeartbeats 200000
namespace Paper.HighGirthOutput

theorem output_cover_and_cardinality
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (∀ r ∈ Paper.HighGirthTransformation.demands G,
      r ∈ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.output G x)) ∧
    (Paper.HighGirthRounding.output G x).card + (Paper.HighGirthRounding.middle G x).card =
      (Paper.HighGirthRounding.first G x).card + (Paper.HighGirthRounding.outside G x).card +
        (Paper.HighGirthRounding.residual G x).card := by
  classical
    let W := Paper.HighGirthRounding.first G x
    let H := Paper.HighGirthRounding.high G x
    let R := Paper.HighGirthRounding.residual G x
    let U := Paper.HighGirthRounding.last G x
    let L := Paper.HighGirthRounding.middle G x
    let D := Paper.HighGirthRounding.output G x
    have hUR : U ⊆ R := Finset.sdiff_subset
    have hWH : Disjoint W H := by
      apply Finset.disjoint_left.mpr
      intro v hw hh
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hh).1).2 hw
    have hWU : Disjoint W U := by
      apply Finset.disjoint_left.mpr
      intro v hw hu
      exact (Finset.mem_sdiff.mp (hUR hu)).2 (Paper.SevenFoundation.subset_covered G W hw)
    have hHU : Disjoint H U := by
      apply Finset.disjoint_left.mpr
      intro v hh hu
      exact (Finset.mem_sdiff.mp hu).2 (Paper.SevenFoundation.subset_covered G H hh)
    have hD : D.card = W.card + H.card + U.card := by
      change ((W ∪ H) ∪ U).card = _
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hWU, hHU⟩),
        Finset.card_union_of_disjoint hWH]
    constructor
    · intro r hr
      have hW : W ⊆ D := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
      have hH : H ⊆ D := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
      by_cases hw : r ∈ Paper.SevenFoundation.covered G W
      · exact Paper.SevenFoundation.covered_mono G hW hw
      have hrR : r ∈ R := Finset.mem_sdiff.mpr ⟨hr, hw⟩
      by_cases hh : r ∈ Paper.SevenFoundation.covered G H
      · exact Paper.SevenFoundation.covered_mono G hH hh
      have hrU : r ∈ U := Finset.mem_sdiff.mpr ⟨hrR, hh⟩
      exact Paper.SevenFoundation.subset_covered G D (Finset.mem_union_right _ hrU)
    · have hsplit := Finset.card_sdiff_add_card_inter R (H ∪ U)
      have hinter : R ∩ (H ∪ U) = (H ∩ R) ∪ U := by
        ext v
        have hu : v ∈ U → v ∈ R := fun hv => hUR hv
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      rw [hinter, Finset.card_union_of_disjoint (hHU.mono_left Finset.inter_subset_left)] at hsplit
      have hHsplit := Finset.card_sdiff_add_card_inter H R
      change L.card + ((H ∩ R).card + U.card) = R.card at hsplit
      change (Paper.HighGirthRounding.outside G x).card + (H ∩ R).card = H.card at hHsplit
      change D.card + L.card = W.card + (Paper.HighGirthRounding.outside G x).card + R.card
      omega

end Paper.HighGirthOutput

#print axioms Paper.HighGirthOutput.output_cover_and_cardinality
