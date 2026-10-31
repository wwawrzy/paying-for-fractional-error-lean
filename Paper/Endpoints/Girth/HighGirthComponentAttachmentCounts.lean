import Paper.Endpoints.Girth.HighGirthComponentAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthComponentAttachmentCounts

theorem component_attachment_counts
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    (Paper.HighGirthComponentAttachments.edges G x K).card =
      (Paper.HighGirthComponentAttachments.pairs G x K).card ∧
    ∀ b : V, Paper.HighGirthFreePaths.members G x K = {b} →
      Paper.HighGirthComponentAttachments.count G x K =
        (G.neighborFinset b ∩ Paper.HighGirthAttachments.connectors G x).card := by
  classical
    have hd := (Paper.HighGirthAttachmentCounts.attachment_count_bounds G x).1
    have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2))
        (Paper.HighGirthComponentAttachments.pairs G x K) := by
      intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp hp).1
      have hq' := (Finset.mem_filter.mp hq).1
      rcases Sym2.mk_eq_mk_iff.mp heq with heq | heq
      · exact heq
      · have hpU := (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
        have hqT := (Finset.mem_product.mp (Finset.mem_filter.mp hq').1).2
        have hswap : p.1 = q.2 := congrArg Prod.fst heq
        exact False.elim ((Finset.disjoint_left.mp hd) hpU (hswap.symm ▸ hqT))
    have he : (Paper.HighGirthComponentAttachments.edges G x K).card =
        (Paper.HighGirthComponentAttachments.pairs G x K).card := Finset.card_image_of_injOn hinj
    refine ⟨he, ?_⟩
    intro b hsingle
    have hbK : b ∈ Paper.HighGirthFreePaths.members G x K := by rw [hsingle]; simp
    have hbU := (Finset.mem_filter.mp hbK).2.1
    have hpairs : Paper.HighGirthComponentAttachments.pairs G x K =
        (G.neighborFinset b ∩ Paper.HighGirthAttachments.connectors G x).image (fun t => (b,t)) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp,hK⟩ := Finset.mem_filter.mp hp
        have hfirst : p.1 = b := by simpa [hsingle] using hK
        obtain ⟨hprod,hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hu,ht⟩ := Finset.mem_product.mp hprod
        refine Finset.mem_image.mpr ⟨p.2, Finset.mem_inter.mpr ⟨?_,ht⟩, ?_⟩
        · exact (G.mem_neighborFinset b p.2).mpr (hfirst ▸ hadj)
        · exact Prod.ext hfirst.symm rfl
      · intro hp
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨hbt,htT⟩ := Finset.mem_inter.mp ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hbU,htT⟩,(G.mem_neighborFinset b t).mp hbt⟩,hbK⟩
    change (Paper.HighGirthComponentAttachments.edges G x K).card = _
    rw [he,hpairs]
    exact Finset.card_image_of_injective _ (fun a c h => congrArg Prod.snd h)

end Paper.HighGirthComponentAttachmentCounts

#print axioms Paper.HighGirthComponentAttachmentCounts.component_attachment_counts
