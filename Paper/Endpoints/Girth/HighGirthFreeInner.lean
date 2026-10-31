import Paper.Endpoints.Girth.HighGirthFreeExternal
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeInner

theorem free_branch_and_inner_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K) :
    (∀ u ∈ Paper.HighGirthFreePaths.members G x K, 3 ≤ G.degree u →
      u ∈ Paper.HighGirthTransformation.branches G ∧
      ∀ y, y ∉ Paper.HighGirthFreePaths.members G x K → G.Adj u y →
        y ∈ Paper.HighGirthAttachments.connectors G x) ∧
    (∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      (G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K).card = 2 →
      u ∉ Paper.HighGirthAttachments.vertices G x →
      ∀ y, G.Adj u y → y ∈ Paper.HighGirthFreePaths.members G x K) := by
  classical
  have hbranch : ∀ u ∈ Paper.HighGirthFreePaths.members G x K, 3 ≤ G.degree u →
      u ∈ Paper.HighGirthTransformation.branches G ∧
      ∀ y, y ∉ Paper.HighGirthFreePaths.members G x K → G.Adj u y →
        y ∈ Paper.HighGirthAttachments.connectors G x := by
    intro u huK hdeg
    have huB : u ∈ Paper.HighGirthTransformation.branches G := by
      simpa only [Paper.HighGirthTransformation.branches,Finset.mem_filter,Finset.mem_univ,true_and] using hdeg
    refine ⟨huB,?_⟩
    intro y hyK huy
    have hyR0 := (Paper.HighGirthFirstSelection.first_selection_geometry G).2
      (Finset.mem_biUnion.mpr ⟨u,huB,(Paper.SevenFoundation.mem_closed G y u).mpr (Or.inr huy)⟩)
    exact (Paper.HighGirthFreeExternal.free_external_neighbors G x K hfree u huK y hyK huy).2.2.1 hyR0
  refine ⟨hbranch,?_⟩
  intro u huK hinner huA y huy
  by_contra hyK
  obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
  have hlow : G.degree u ≤ 2 := by
    by_contra hn
    have ht := (hbranch u huK (by omega)).2 y hyK huy
    exact huA (Finset.mem_filter.mpr ⟨huU,⟨y,ht,huy⟩⟩)
  let A := G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K
  have hA : A.card = 2 := hinner
  have hyA : y ∉ A := fun h => hyK (Finset.mem_inter.mp h).2
  have hsub : insert y A ⊆ G.neighborFinset u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (G.mem_neighborFinset _ _).mpr huy
    · exact (Finset.mem_inter.mp hz).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyA,hA,SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

end Paper.HighGirthFreeInner

#print axioms Paper.HighGirthFreeInner.free_branch_and_inner_neighbors
