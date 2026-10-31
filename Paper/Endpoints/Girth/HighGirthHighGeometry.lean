import Paper.Endpoints.Girth.HighGirthRounding
set_option maxHeartbeats 200000
namespace Paper.HighGirthHighGeometry

theorem high_vertex_geometry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (v : V) (hv : v ∈ Paper.HighGirthRounding.high G x) :
    3 ≤ G.degree v ∧ v ∈ Paper.HighGirthTransformation.demands G ∧
      Paper.HighGirthTransformation.candidateCost G v = 3 ∧ x v ≤ (1 : Real) / 2 := by
  classical
    obtain ⟨hvZW, hhits⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvZ, hvW⟩ := Finset.mem_sdiff.mp hvZW
    have hdeg : 3 ≤ G.degree v := by
      have hc := Finset.card_le_card (Finset.inter_subset_left :
        Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x ⊆ Paper.SevenFoundation.closed G v)
      rw [Paper.WeightedBudget.closed_card G v] at hc
      change 4 ≤ (Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x).card at hhits
      omega
    have hvB : v ∈ Paper.HighGirthTransformation.branches G := by
      simp only [Paper.HighGirthTransformation.branches, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdeg
    have hvR := (Paper.HighGirthFirstSelection.first_selection_geometry G).2
      (Paper.SevenFoundation.subset_covered G _ hvB)
    have hcost := (Paper.HighGirthCostThree.cost_three_iff_demand G v hvZ).mpr hvR
    refine ⟨hdeg, hvR, hcost, ?_⟩
    by_contra hx
    apply hvW
    exact Finset.mem_filter.mpr ⟨hvZ, hcost, lt_of_not_ge hx⟩

end Paper.HighGirthHighGeometry

#print axioms Paper.HighGirthHighGeometry.high_vertex_geometry
