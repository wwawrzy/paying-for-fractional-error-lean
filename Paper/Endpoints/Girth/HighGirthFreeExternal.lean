import Paper.Endpoints.Girth.HighGirthFreePaths
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeExternal

theorem free_external_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K) :
    ∀ u ∈ Paper.HighGirthFreePaths.members G x K, ∀ y,
      y ∉ Paper.HighGirthFreePaths.members G x K → G.Adj u y →
      y ∉ Paper.HighGirthRounding.residual G x ∧
      y ∈ Paper.HighGirthTransformation.zone G ∧
      (y ∈ Paper.HighGirthTransformation.demands G → y ∈ Paper.HighGirthAttachments.connectors G x) ∧
      (y ∉ Paper.HighGirthTransformation.demands G →
        y ∈ Paper.HighGirthRounding.positive G x ∧ Paper.HighGirthRounding.hits G x y ≤ 1) := by
  classical
  intro u huK y hyK huy
  obtain ⟨hu,huComp⟩ := (Finset.mem_filter.mp huK).2
  have huR0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1
  have hyH : y ∉ Paper.HighGirthRounding.high G x := by
    intro hy
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr
      ⟨y,hy,(Paper.SevenFoundation.mem_closed G u y).mpr (Or.inr huy.symm)⟩)
  have hyU : y ∉ Paper.HighGirthRounding.last G x := by
    intro hy
    apply hyK
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hy, ?_⟩
    have hadj : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).Adj ⟨u,hu⟩ ⟨y,hy⟩ := huy
    exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans huComp
  have hyR : y ∉ Paper.HighGirthRounding.residual G x := by
    intro hy
    have hyL : y ∈ Paper.HighGirthRounding.middle G x := Finset.mem_sdiff.mpr
      ⟨hy,fun h => (Finset.mem_union.mp h).elim hyH hyU⟩
    exact hfree u huK y hyL huy
  have hyZ : y ∈ Paper.HighGirthTransformation.zone G :=
    (Paper.HighGirthRestriction.restriction_feasible G).1 u huR0
      ((Paper.SevenFoundation.mem_closed G y u).mpr (Or.inr huy))
  refine ⟨hyR,hyZ,?_,?_⟩
  · intro hyR0
    exact (Paper.HighGirthResidualAttachments.residual_attachments G x).1 u hu y
      (Finset.mem_sdiff.mpr ⟨hyR0,hyR⟩) huy
  · intro hyR0
    have hcNe : Paper.HighGirthTransformation.candidateCost G y ≠ 3 :=
      fun h => hyR0 ((Paper.HighGirthCostThree.cost_three_iff_demand G y hyZ).mp h)
    have hcBound := Paper.HighGirthCostBounds.candidate_cost_bounds G y hyZ
    have hcLt : Paper.HighGirthTransformation.candidateCost G y < 3 := by omega
    have hyW : y ∉ Paper.HighGirthRounding.first G x := by
      intro hy
      exact hcNe (Finset.mem_filter.mp hy).2.1
    have hyO : y ∈ Paper.HighGirthRounding.other G x := Finset.mem_sdiff.mpr
      ⟨hyZ,fun h => (Finset.mem_union.mp h).elim hyW hyH⟩
    have hgap := (Paper.HighGirthOtherGeometry.remaining_candidate_geometry G x y hyO).2 hcLt
    have hhit : Paper.HighGirthRounding.hits G x y ≤ 1 := by omega
    exact ⟨Finset.mem_filter.mpr ⟨hyO,by omega⟩,hhit⟩

end Paper.HighGirthFreeExternal

#print axioms Paper.HighGirthFreeExternal.free_external_neighbors
