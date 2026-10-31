import Paper.Endpoints.Girth.HighGirthOneAttachment
set_option maxHeartbeats 200000
namespace Paper.HighGirthBranchAttachment

theorem branch_with_one_connector_is_inner
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K)
    (u : V) (huK : u ∈ Paper.HighGirthFreePaths.members G x K)
    (huB : u ∈ Paper.HighGirthTransformation.branches G)
    (hT : (G.neighborFinset u ∩ Paper.HighGirthAttachments.connectors G x).card ≤ 1) :
    2 ≤ (G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K).card := by
  classical
  let A := G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K
  let T := G.neighborFinset u ∩ Paper.HighGirthAttachments.connectors G x
  have hdeg : 3 ≤ G.degree u := (Finset.mem_filter.mp huB).2
  have hext := (Paper.HighGirthFreeInner.free_branch_and_inner_neighbors G x K hfree).1 u huK hdeg
  have hsub : G.neighborFinset u ⊆ A ∪ T := by
    intro v hv
    by_cases hvK : v ∈ Paper.HighGirthFreePaths.members G x K
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv,hvK⟩)
    · have hvT := hext.2 v hvK ((G.mem_neighborFinset u v).mp hv)
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv,hvT⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A T)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hbound : 3 ≤ A.card + T.card := hdeg.trans hc
  change T.card ≤ 1 at hT
  change 2 ≤ A.card
  omega

end Paper.HighGirthBranchAttachment

#print axioms Paper.HighGirthBranchAttachment.branch_with_one_connector_is_inner
