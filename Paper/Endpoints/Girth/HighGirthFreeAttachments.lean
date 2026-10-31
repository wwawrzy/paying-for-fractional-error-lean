import Paper.Endpoints.Girth.HighGirthFreeAccess

namespace Paper.HighGirthFreeAttachments

theorem branches_and_attachment_exists
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.free G x K) :
    (∀ u ∈ HighGirthTransformation.branches G ∩ HighGirthFreePaths.members G x K,
      u ∈ HighGirthAttachments.vertices G x) ∧
    (∃ u ∈ HighGirthFreePaths.members G x K, u ∈ HighGirthAttachments.vertices G x) := by
  classical
  have hbranch : ∀ u ∈ HighGirthTransformation.branches G ∩ HighGirthFreePaths.members G x K,
      u ∈ HighGirthAttachments.vertices G x := by
    intro u hu
    obtain ⟨huB,huK⟩ := Finset.mem_inter.mp hu
    obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
    exact (HighGirthResidualAttachments.residual_attachments G x).2 u (Finset.mem_inter.mpr ⟨huB,huU⟩)
  refine ⟨hbranch,?_⟩
  obtain ⟨a⟩ := K.connected_toSimpleGraph.nonempty
  have haK : a.val.val ∈ HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
  rcases HighGirthFreeAccess.free_short_access G x K hfree a.val.val haK with
    ⟨b,hb,hbU,huU,q,hq,hlen,hs⟩ | ⟨b,hb,hbU,huU,q,hq,hlen,hs⟩
  · exact ⟨b,(Finset.mem_inter.mp hb).2,hbranch b hb⟩
  · exact ⟨b,(Finset.mem_inter.mp hb).2,(Finset.mem_inter.mp hb).1⟩

end Paper.HighGirthFreeAttachments

#print axioms Paper.HighGirthFreeAttachments.branches_and_attachment_exists
