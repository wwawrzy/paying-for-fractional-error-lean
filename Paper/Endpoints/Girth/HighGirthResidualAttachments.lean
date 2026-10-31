import Paper.Endpoints.Girth.HighGirthAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualAttachments

theorem residual_attachments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (∀ u ∈ Paper.HighGirthRounding.last G x,
      ∀ v ∈ Paper.HighGirthTransformation.demands G \ Paper.HighGirthRounding.residual G x,
        G.Adj u v → v ∈ Paper.HighGirthAttachments.connectors G x) ∧
    (∀ u ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthRounding.last G x,
      u ∈ Paper.HighGirthAttachments.vertices G x) := by
  classical
    have hext : ∀ u ∈ Paper.HighGirthRounding.last G x,
        ∀ v ∈ Paper.HighGirthTransformation.demands G \ Paper.HighGirthRounding.residual G x,
          G.Adj u v → v ∈ Paper.HighGirthAttachments.connectors G x := by
      intro u hu v hv hadj
      obtain ⟨hvR0, hvR⟩ := Finset.mem_sdiff.mp hv
      have huR : u ∈ Paper.HighGirthRounding.residual G x := (Finset.mem_sdiff.mp hu).1
      have hvW : v ∉ Paper.HighGirthRounding.first G x := by
        intro hw
        exact (Finset.mem_sdiff.mp huR).2 (Finset.mem_biUnion.mpr ⟨v, hw,
          (Paper.SevenFoundation.mem_closed G u v).mpr (Or.inr hadj.symm)⟩)
      have hvCovered : v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.first G x) := by
        by_contra hn
        exact hvR (Finset.mem_sdiff.mpr ⟨hvR0, hn⟩)
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hvCovered
      have hne : v ≠ w := by
        intro heq
        subst v
        exact hvW hw
      have hwv := ((Paper.SevenFoundation.mem_closed G v w).mp hvw).resolve_left hne
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvW, ⟨w, hw, hwv.symm⟩, ⟨u, hu, hadj.symm⟩⟩
    refine ⟨hext, ?_⟩
    intro u hu
    obtain ⟨huB, huU⟩ := Finset.mem_inter.mp hu
    have hbranch : 3 ≤ G.degree u := (Finset.mem_filter.mp huB).2
    have hlow := Paper.HighGirthResidualDegree.residual_neighbor_degree G x u
      (Finset.mem_sdiff.mp huU).1 (Or.inl huU)
    have hex : ∃ v ∈ G.neighborFinset u, v ∉ Paper.HighGirthRounding.residual G x := by
      by_contra hn
      push_neg at hn
      have heq : G.neighborFinset u ∩ Paper.HighGirthRounding.residual G x = G.neighborFinset u :=
        Finset.inter_eq_left.mpr hn
      rw [heq, SimpleGraph.card_neighborFinset_eq_degree] at hlow
      omega
    obtain ⟨v, huv, hvR⟩ := hex
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp huv
    have hvR0 := (Paper.HighGirthFirstSelection.first_selection_geometry G).2
      (Finset.mem_biUnion.mpr ⟨u, huB, (Paper.SevenFoundation.mem_closed G v u).mpr (Or.inr hadj)⟩)
    have hvT := hext u huU v (Finset.mem_sdiff.mpr ⟨hvR0, hvR⟩) hadj
    exact Finset.mem_filter.mpr ⟨huU, ⟨v, hvT, hadj⟩⟩

end Paper.HighGirthResidualAttachments

#print axioms Paper.HighGirthResidualAttachments.residual_attachments
