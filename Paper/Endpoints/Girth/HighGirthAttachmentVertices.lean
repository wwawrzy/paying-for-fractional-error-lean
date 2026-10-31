import Paper.Endpoints.Girth.HighGirthBranchPathCharge
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentVertices

theorem attachment_vertices_exhausted
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hcount : Paper.HighGirthComponentAttachments.count G x K ≤ 2)
    (a b : V) (haK : a ∈ Paper.HighGirthFreePaths.members G x K)
    (hbK : b ∈ Paper.HighGirthFreePaths.members G x K) (hab : a ≠ b)
    (haA : a ∈ Paper.HighGirthAttachments.vertices G x)
    (hbA : b ∈ Paper.HighGirthAttachments.vertices G x) :
    ∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      u ∈ Paper.HighGirthAttachments.vertices G x → u = a ∨ u = b := by
  classical
  intro u huK huA
  by_contra hn
  push_neg at hn
  obtain ⟨s,hs,has⟩ := (Finset.mem_filter.mp haA).2
  obtain ⟨t,ht,hbt⟩ := (Finset.mem_filter.mp hbA).2
  obtain ⟨w,hw,huw⟩ := (Finset.mem_filter.mp huA).2
  have haU := (Finset.mem_filter.mp haK).2.1
  have hbU := (Finset.mem_filter.mp hbK).2.1
  have huU := (Finset.mem_filter.mp huK).2.1
  have hp1 : (a,s) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haU,hs⟩,has⟩,haK⟩
  have hp2 : (b,t) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbU,ht⟩,hbt⟩,hbK⟩
  have hp3 : (u,w) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huU,hw⟩,huw⟩,huK⟩
  have hthree : 2 < (Paper.HighGirthComponentAttachments.pairs G x K).card :=
    Finset.two_lt_card_iff.mpr ⟨(a,s),(b,t),(u,w),hp1,hp2,hp3,
      (fun h => hab (congrArg Prod.fst h)),
      (fun h => hn.1 (congrArg Prod.fst h).symm),
      (fun h => hn.2 (congrArg Prod.fst h).symm)⟩
  have he := (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1
  change (Paper.HighGirthComponentAttachments.edges G x K).card ≤ 2 at hcount
  omega

end Paper.HighGirthAttachmentVertices

#print axioms Paper.HighGirthAttachmentVertices.attachment_vertices_exhausted
