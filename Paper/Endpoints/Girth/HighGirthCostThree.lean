import Paper.Endpoints.Girth.HighGirthCostBounds
set_option maxHeartbeats 200000
namespace Paper.HighGirthCostThree

theorem cost_three_iff_demand
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : v ∈ Paper.HighGirthTransformation.zone G) :
    Paper.HighGirthTransformation.candidateCost G v = 3 ↔
      v ∈ Paper.HighGirthTransformation.demands G := by
  have hvF : v ∉ Paper.HighGirthTransformation.far G :=
    fun h => (Finset.mem_sdiff.mp h).2 hv
  have hmem : v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.far G) ↔
      (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).Nonempty := by
    constructor
    · intro h
      obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp h
      have huv := (Paper.SevenFoundation.closed_symm G v u).mp hvu
      rcases (Paper.SevenFoundation.mem_closed G u v).mp huv with heq | hadj
      · subst u
        exact False.elim (hvF hu)
      · exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr hadj, hu⟩⟩
    · rintro ⟨u, hu⟩
      obtain ⟨hun, huF⟩ := Finset.mem_inter.mp hu
      exact Finset.mem_biUnion.mpr ⟨u, huF,
        (Paper.SevenFoundation.closed_symm G v u).mpr
          ((Paper.SevenFoundation.mem_closed G u v).mpr
            (Or.inr ((G.mem_neighborFinset v u).mp hun)))⟩
  have hzero : Paper.HighGirthTransformation.candidateCost G v = 3 ↔
      (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card = 0 := by
    dsimp only [Paper.HighGirthTransformation.candidateCost]
    omega
  constructor
  · intro hc
    refine Finset.mem_sdiff.mpr ⟨hv, ?_⟩
    intro hcovered
    have hp := Finset.card_pos.mpr (hmem.mp hcovered)
    have hz := hzero.mp hc
    omega
  · intro hvR
    apply hzero.mpr
    by_contra hn
    have hp : 0 < (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card := by omega
    exact (Finset.mem_sdiff.mp hvR).2 (hmem.mpr (Finset.card_pos.mp hp))

end Paper.HighGirthCostThree

#print axioms Paper.HighGirthCostThree.cost_three_iff_demand
