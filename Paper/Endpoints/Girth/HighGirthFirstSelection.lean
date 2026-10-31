import Paper.Endpoints.Girth.HighGirthTransformation
set_option maxHeartbeats 200000
namespace Paper.HighGirthFirstSelection

theorem first_selection_geometry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ v ∈ Paper.HighGirthTransformation.far G, G.degree v ≤ 2) ∧
      Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.branches G) ⊆
        Paper.HighGirthTransformation.demands G := by
  constructor
  · intro v hv
    by_contra hdeg
    have hvB : v ∈ Paper.HighGirthTransformation.branches G := by
      simp only [Paper.HighGirthTransformation.branches, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hvZ : v ∈ Paper.HighGirthTransformation.zone G :=
      Paper.SevenFoundation.subset_covered G _ (Paper.SevenFoundation.subset_covered G _ hvB)
    exact (Finset.mem_sdiff.mp hv).2 hvZ
  · intro v hv
    refine Finset.mem_sdiff.mpr ⟨Paper.SevenFoundation.subset_covered G _ hv, ?_⟩
    intro hcovered
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hcovered
    have huZ : u ∈ Paper.HighGirthTransformation.zone G :=
      Finset.mem_biUnion.mpr ⟨v, hv, (Paper.SevenFoundation.closed_symm G v u).mp hvu⟩
    exact (Finset.mem_sdiff.mp hu).2 huZ

end Paper.HighGirthFirstSelection

#print axioms Paper.HighGirthFirstSelection.first_selection_geometry
