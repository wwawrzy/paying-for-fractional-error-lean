import Paper.Endpoints.Girth.HighGirthHighGeometry
set_option maxHeartbeats 200000
namespace Paper.HighGirthOtherGeometry

theorem remaining_candidate_geometry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (v : V) (hv : v ∈ Paper.HighGirthRounding.other G x) :
    Paper.HighGirthRounding.hits G x v ≤ Paper.HighGirthTransformation.candidateCost G v ∧
      (Paper.HighGirthTransformation.candidateCost G v < 3 →
        Paper.HighGirthRounding.hits G x v + 1 ≤ Paper.HighGirthTransformation.candidateCost G v) := by
  classical
    obtain ⟨hvZ, hvWH⟩ := Finset.mem_sdiff.mp hv
    have hvW : v ∉ Paper.HighGirthRounding.first G x := fun h => hvWH (Finset.mem_union_left _ h)
    have hvH : v ∉ Paper.HighGirthRounding.high G x := fun h => hvWH (Finset.mem_union_right _ h)
    have hh : Paper.HighGirthRounding.hits G x v ≤ 3 := by
      by_contra h
      apply hvH
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvZ, hvW⟩, by omega⟩
    have hb := Paper.HighGirthCostBounds.candidate_cost_bounds G v hvZ
    have hcheap : Paper.HighGirthTransformation.candidateCost G v < 3 →
        Paper.HighGirthRounding.hits G x v + 1 ≤ Paper.HighGirthTransformation.candidateCost G v := by
      intro hc
      have hsub : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x ⊆
          Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.demands G := by
        intro u hu
        obtain ⟨huv, huR⟩ := Finset.mem_inter.mp hu
        exact Finset.mem_inter.mpr ⟨huv, (Finset.mem_sdiff.mp huR).1⟩
      have hcard := Finset.card_le_card hsub
      have hbudget := Paper.HighGirthCheapDemands.cheap_candidate_demands G v hvZ hc
      change Paper.HighGirthRounding.hits G x v ≤ _ at hcard
      omega
    refine ⟨?_, hcheap⟩
    by_cases hc : Paper.HighGirthTransformation.candidateCost G v < 3
    · have h := hcheap hc
      omega
    · omega

end Paper.HighGirthOtherGeometry

#print axioms Paper.HighGirthOtherGeometry.remaining_candidate_geometry
