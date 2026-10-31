import Paper.Endpoints.Girth.HighGirthFirstSelection
set_option maxHeartbeats 200000
namespace Paper.HighGirthCostBounds

theorem candidate_cost_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : v ∈ Paper.HighGirthTransformation.zone G) :
    1 ≤ Paper.HighGirthTransformation.candidateCost G v ∧
      Paper.HighGirthTransformation.candidateCost G v ≤ 3 ∧
      (Paper.HighGirthTransformation.candidateCost G v < 3 → G.degree v ≤ 2) := by
  have hdeg : 0 < (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card →
      G.degree v ≤ 2 := by
    intro hpos
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    obtain ⟨huv, huF⟩ := Finset.mem_inter.mp hu
    by_contra hlarge
    have hvB : v ∈ Paper.HighGirthTransformation.branches G := by
      simp only [Paper.HighGirthTransformation.branches, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have huNear : u ∈ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.branches G) :=
      Finset.mem_biUnion.mpr ⟨v, hvB, (Paper.SevenFoundation.mem_closed G u v).mpr
        (Or.inr ((G.mem_neighborFinset v u).mp huv))⟩
    have huR := (Paper.HighGirthFirstSelection.first_selection_geometry G).2 huNear
    exact (Finset.mem_sdiff.mp huF).2 (Finset.mem_sdiff.mp huR).1
  have hcard : (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card ≤ 2 := by
    by_cases hz : (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card = 0
    · omega
    have hle := Finset.card_le_card
      (Finset.inter_subset_left : G.neighborFinset v ∩ Paper.HighGirthTransformation.far G ⊆ G.neighborFinset v)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
    exact hle.trans (hdeg (by omega))
  have hcost : 1 ≤ Paper.HighGirthTransformation.candidateCost G v ∧
      Paper.HighGirthTransformation.candidateCost G v ≤ 3 := by
    dsimp only [Paper.HighGirthTransformation.candidateCost]
    omega
  refine ⟨hcost.1, hcost.2, ?_⟩
  intro hcheap
  apply hdeg
  dsimp only [Paper.HighGirthTransformation.candidateCost] at hcheap
  omega

end Paper.HighGirthCostBounds

#print axioms Paper.HighGirthCostBounds.candidate_cost_bounds
