import Paper.Endpoints.Girth.HighGirthFreeAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeEndpoints

theorem free_endpoint_positive
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K) :
    ∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      (G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K).card ≤ 1 →
      u ∈ Paper.HighGirthRounding.positive G x := by
  classical
  intro u huK hend
  obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
  have huR := (Finset.mem_sdiff.mp huU).1
  have huR0 := (Finset.mem_sdiff.mp huR).1
  have huZ := (Finset.mem_sdiff.mp huR0).1
  have huW : u ∉ Paper.HighGirthRounding.first G x := by
    intro h
    exact (Finset.mem_sdiff.mp huR).2 (Paper.SevenFoundation.subset_covered G _ h)
  have huH : u ∉ Paper.HighGirthRounding.high G x := by
    intro h
    exact (Finset.mem_sdiff.mp huU).2 (Paper.SevenFoundation.subset_covered G _ h)
  have huO : u ∈ Paper.HighGirthRounding.other G x := Finset.mem_sdiff.mpr
    ⟨huZ,fun h => (Finset.mem_union.mp h).elim huW huH⟩
  have hcost := (Paper.HighGirthCostThree.cost_three_iff_demand G u huZ).mpr huR0
  let A := G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K
  have hsub : Paper.SevenFoundation.closed G u ∩ Paper.HighGirthRounding.residual G x ⊆ insert u A := by
    intro z hz
    obtain ⟨hzu,hzR⟩ := Finset.mem_inter.mp hz
    rcases (Paper.SevenFoundation.mem_closed G z u).mp hzu with heq | huz
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · have hzK : z ∈ Paper.HighGirthFreePaths.members G x K := by
        by_contra hn
        exact (Paper.HighGirthFreeExternal.free_external_neighbors G x K hfree u huK z hn huz).1 hzR
      exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u z).mpr huz,hzK⟩)
  have hh : Paper.HighGirthRounding.hits G x u ≤ 2 := by
    calc
      _ ≤ (insert u A).card := Finset.card_le_card hsub
      _ ≤ A.card + 1 := Finset.card_insert_le u A
      _ ≤ 2 := by change (G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K).card + 1 ≤ 2; omega
  exact Finset.mem_filter.mpr ⟨huO,by omega⟩

end Paper.HighGirthFreeEndpoints

#print axioms Paper.HighGirthFreeEndpoints.free_endpoint_positive
