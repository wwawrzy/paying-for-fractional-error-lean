import Paper.Endpoints.Girth.HighGirthCostThree
import Paper.Endpoints.Rounding.SelectionGeometry
set_option maxHeartbeats 200000
namespace Paper.HighGirthCheapDemands

theorem cheap_candidate_demands
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : v ∈ Paper.HighGirthTransformation.zone G)
    (hcheap : Paper.HighGirthTransformation.candidateCost G v < 3) :
    (Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.demands G).card ≤
      Paper.HighGirthTransformation.candidateCost G v - 1 := by
  have hvR : v ∉ Paper.HighGirthTransformation.demands G := by
    intro h
    have he := (Paper.HighGirthCostThree.cost_three_iff_demand G v hv).mpr h
    omega
  have hvF : v ∉ Paper.HighGirthTransformation.far G :=
    fun h => (Finset.mem_sdiff.mp h).2 hv
  have hdisjoint : Disjoint (Paper.HighGirthTransformation.demands G)
      (Paper.HighGirthTransformation.far G) := by
    apply Finset.disjoint_left.mpr
    intro u huR huF
    exact (Finset.mem_sdiff.mp huF).2 (Finset.mem_sdiff.mp huR).1
  have hcount := Paper.SelectionGeometry.two_parts_le_degree G
    (Paper.HighGirthTransformation.demands G) (Paper.HighGirthTransformation.far G) v
    hdisjoint hvR hvF
  have hinter : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G =
      G.neighborFinset v ∩ Paper.HighGirthTransformation.far G := by
    ext u
    constructor
    · intro h
      obtain ⟨huv, huF⟩ := Finset.mem_inter.mp h
      have hne : u ≠ v := by
        intro heq
        subst u
        exact hvF huF
      have hadj := ((Paper.SevenFoundation.mem_closed G u v).mp huv).resolve_left hne
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr hadj, huF⟩
    · intro h
      obtain ⟨huv, huF⟩ := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨(Paper.SevenFoundation.mem_closed G u v).mpr
        (Or.inr ((G.mem_neighborFinset v u).mp huv)), huF⟩
  rw [hinter] at hcount
  have hdeg := (Paper.HighGirthCostBounds.candidate_cost_bounds G v hv).2.2 hcheap
  dsimp only [Paper.HighGirthTransformation.candidateCost]
  omega

end Paper.HighGirthCheapDemands

#print axioms Paper.HighGirthCheapDemands.cheap_candidate_demands
