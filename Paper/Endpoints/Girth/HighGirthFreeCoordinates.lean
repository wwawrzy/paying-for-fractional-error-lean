import Paper.Endpoints.Girth.HighGirthResidual
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeCoordinates

theorem residual_threshold_coordinates
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (∀ u ∈ Paper.HighGirthRounding.last G x, x u ≤ (1 : Real) / 2) ∧
    (∀ t ∈ Paper.HighGirthAttachments.connectors G x,
      t ∈ Paper.HighGirthRounding.other G x ∧
      (t ∈ Paper.HighGirthRounding.positive G x ∨ x t ≤ (1 : Real) / 2)) := by
  classical
    have hhalf : ∀ v ∈ Paper.HighGirthTransformation.demands G,
        v ∉ Paper.HighGirthRounding.first G x → x v ≤ (1 : Real) / 2 := by
      intro v hv hvW
      have hvZ := (Finset.mem_sdiff.mp hv).1
      have hc := (Paper.HighGirthCostThree.cost_three_iff_demand G v hvZ).mpr hv
      by_contra hn
      apply hvW
      exact Finset.mem_filter.mpr ⟨hvZ, hc, by linarith⟩
    constructor
    · intro u hu
      have huR := (Finset.mem_sdiff.mp hu).1
      have huR0 := (Finset.mem_sdiff.mp huR).1
      apply hhalf u huR0
      intro huW
      exact (Finset.mem_sdiff.mp huR).2
        (Paper.SevenFoundation.subset_covered G _ huW)
    · intro t ht
      obtain ⟨htW, hw, u, hu, htu⟩ := (Finset.mem_filter.mp ht).2
      have huR0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1
      have htZ : t ∈ Paper.HighGirthTransformation.zone G :=
        (Paper.HighGirthRestriction.restriction_feasible G).1 u huR0
          ((Paper.SevenFoundation.mem_closed G t u).mpr (Or.inr htu.symm))
      have htH : t ∉ Paper.HighGirthRounding.high G x := by
        intro h
        exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr
          ⟨t, h, (Paper.SevenFoundation.mem_closed G u t).mpr (Or.inr htu)⟩)
      have htO : t ∈ Paper.HighGirthRounding.other G x := Finset.mem_sdiff.mpr
        ⟨htZ, fun h => (Finset.mem_union.mp h).elim htW htH⟩
      refine ⟨htO, ?_⟩
      by_cases htP : t ∈ Paper.HighGirthRounding.positive G x
      · exact Or.inl htP
      · right
        have hnot : ¬ Paper.HighGirthRounding.hits G x t < Paper.HighGirthTransformation.candidateCost G t :=
          fun h => htP (Finset.mem_filter.mpr ⟨htO,h⟩)
        have hgeom := Paper.HighGirthOtherGeometry.remaining_candidate_geometry G x t htO
        have hcost := Paper.HighGirthCostBounds.candidate_cost_bounds G t htZ
        have hc : Paper.HighGirthTransformation.candidateCost G t = 3 := by
          by_contra hn
          have hlt : Paper.HighGirthTransformation.candidateCost G t < 3 := by omega
          have hh := hgeom.2 hlt
          omega
        exact hhalf t ((Paper.HighGirthCostThree.cost_three_iff_demand G t htZ).mp hc) htW

end Paper.HighGirthFreeCoordinates

#print axioms Paper.HighGirthFreeCoordinates.residual_threshold_coordinates
