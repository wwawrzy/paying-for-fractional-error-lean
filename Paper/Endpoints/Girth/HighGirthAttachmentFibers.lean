import Paper.Endpoints.Girth.HighGirthBranchAttachment
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentFibers

theorem connector_fiber_at_most_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hcount : Paper.HighGirthComponentAttachments.count G x K ≤ 2)
    (u v : V) (huK : u ∈ Paper.HighGirthFreePaths.members G x K)
    (hvK : v ∈ Paper.HighGirthFreePaths.members G x K) (huv : u ≠ v)
    (hvA : v ∈ Paper.HighGirthAttachments.vertices G x) :
    (G.neighborFinset u ∩ Paper.HighGirthAttachments.connectors G x).card ≤ 1 := by
  classical
  by_contra hn
  have hc : 1 < (G.neighborFinset u ∩ Paper.HighGirthAttachments.connectors G x).card := by omega
  obtain ⟨s,hs,t,ht,hst⟩ := Finset.one_lt_card.mp hc
  obtain ⟨hsN,hsT⟩ := Finset.mem_inter.mp hs
  obtain ⟨htN,htT⟩ := Finset.mem_inter.mp ht
  obtain ⟨w,hwT,hvw⟩ := (Finset.mem_filter.mp hvA).2
  have huU := (Finset.mem_filter.mp huK).2.1
  have hvU := (Finset.mem_filter.mp hvK).2.1
  have hp1 : (u,s) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨huU,hsT⟩,(G.mem_neighborFinset u s).mp hsN⟩,huK⟩
  have hp2 : (u,t) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨huU,htT⟩,(G.mem_neighborFinset u t).mp htN⟩,huK⟩
  have hp3 : (v,w) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hvU,hwT⟩,hvw⟩,hvK⟩
  have hthree : 2 < (Paper.HighGirthComponentAttachments.pairs G x K).card := by
    apply Finset.two_lt_card_iff.mpr
    exact ⟨(u,s),(u,t),(v,w),hp1,hp2,hp3,
      (fun h => hst (congrArg Prod.snd h)),
      (fun h => huv (congrArg Prod.fst h)),
      (fun h => huv (congrArg Prod.fst h))⟩
  have he := (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1
  change (Paper.HighGirthComponentAttachments.edges G x K).card ≤ 2 at hcount
  omega

end Paper.HighGirthAttachmentFibers

#print axioms Paper.HighGirthAttachmentFibers.connector_fiber_at_most_one
