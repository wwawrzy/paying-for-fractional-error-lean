import Paper.Endpoints.Girth.HighGirthAuxiliary
set_option maxHeartbeats 200000
namespace Paper.HighGirthRestriction

theorem restriction_feasible
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ r ∈ Paper.HighGirthTransformation.demands G,
      Paper.SevenFoundation.closed G r ⊆ Paper.HighGirthTransformation.zone G) ∧
    (∀ y : V → Real, Paper.SevenFoundation.feasible (Paper.SevenFoundation.ordinary G) y →
      Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G)
        (Paper.HighGirthAuxiliary.restrict G y)) := by
  have hsubset : ∀ r ∈ Paper.HighGirthTransformation.demands G,
      Paper.SevenFoundation.closed G r ⊆ Paper.HighGirthTransformation.zone G := by
    intro r hr v hv
    by_contra hn
    have hvF : v ∈ Paper.HighGirthTransformation.far G :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
    exact (Finset.mem_sdiff.mp hr).2
      (Finset.mem_biUnion.mpr ⟨v, hvF, (Paper.SevenFoundation.closed_symm G v r).mp hv⟩)
  refine ⟨hsubset, ?_⟩
  intro y hy
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp only [Paper.HighGirthAuxiliary.restrict]
    split_ifs <;> first | exact hy.1 v | exact le_refl _
  · intro v hv
    change v ∉ Paper.HighGirthTransformation.zone G at hv
    simp [Paper.HighGirthAuxiliary.restrict, hv]
  · intro r hr
    change r ∈ Paper.HighGirthTransformation.demands G at hr
    have hs := hsubset r hr
    have heq : Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G =
        Paper.SevenFoundation.closed G r := Finset.inter_eq_left.mpr hs
    change 1 ≤ ∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G,
      Paper.HighGirthAuxiliary.restrict G y v
    rw [heq]
    have heqsum : (∑ v ∈ Paper.SevenFoundation.closed G r, Paper.HighGirthAuxiliary.restrict G y v) =
        ∑ v ∈ Paper.SevenFoundation.closed G r, y v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [Paper.HighGirthAuxiliary.restrict, hs hv]
    rw [heqsum]
    exact hy.2.2 r (Finset.mem_univ _)

end Paper.HighGirthRestriction

#print axioms Paper.HighGirthRestriction.restriction_feasible
