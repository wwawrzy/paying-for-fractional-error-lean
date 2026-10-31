import Paper.Endpoints.Girth.HighGirthSaving
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualDegree

theorem residual_neighbor_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (v : V) (hvR : v ∈ Paper.HighGirthRounding.residual G x)
    (hnear : v ∈ Paper.HighGirthRounding.last G x ∨
      ∃ u ∈ Paper.HighGirthRounding.last G x, G.Adj v u) :
    (G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x).card ≤ 2 := by
  classical
    have hvR0 : v ∈ Paper.HighGirthTransformation.demands G := (Finset.mem_sdiff.mp hvR).1
    have hvZ : v ∈ Paper.HighGirthTransformation.zone G := (Finset.mem_sdiff.mp hvR0).1
    have hvW : v ∉ Paper.HighGirthRounding.first G x := by
      intro hw
      exact (Finset.mem_sdiff.mp hvR).2
        (Paper.SevenFoundation.subset_covered G (Paper.HighGirthRounding.first G x) hw)
    have hvH : v ∉ Paper.HighGirthRounding.high G x := by
      intro hh
      rcases hnear with hu | ⟨u, hu, hadj⟩
      · exact (Finset.mem_sdiff.mp hu).2
          (Paper.SevenFoundation.subset_covered G (Paper.HighGirthRounding.high G x) hh)
      · exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨v, hh,
          (Paper.SevenFoundation.mem_closed G u v).mpr (Or.inr hadj)⟩)
    have hhits : Paper.HighGirthRounding.hits G x v ≤ 3 := by
      by_contra hn
      exact hvH (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvZ, hvW⟩, by omega⟩)
    have heq : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x =
        insert v (G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x) := by
      ext u
      simp only [Finset.mem_inter, Paper.SevenFoundation.mem_closed, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨(heq | hadj), huR⟩
        · exact Or.inl heq
        · exact Or.inr ⟨hadj, huR⟩
      · rintro (heq | ⟨hadj, huR⟩)
        · subst u
          exact ⟨Or.inl rfl, hvR⟩
        · exact ⟨Or.inr hadj, huR⟩
    have hself : v ∉ G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x := by simp
    have hcard : Paper.HighGirthRounding.hits G x v =
        (G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x).card + 1 := by
      unfold Paper.HighGirthRounding.hits
      rw [heq, Finset.card_insert_of_notMem hself]
    omega

end Paper.HighGirthResidualDegree

#print axioms Paper.HighGirthResidualDegree.residual_neighbor_degree
