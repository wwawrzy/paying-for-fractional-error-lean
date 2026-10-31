import Paper.Endpoints.Girth.HighGirthComponentAttachmentCounts
set_option maxHeartbeats 200000
namespace Paper.HighGirthOneAttachmentCharge

theorem one_attachment_charge
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (hcount : Paper.HighGirthComponentAttachments.count G x K ≤ 1) :
    (1 : Real) / 2 ≤ Paper.HighGirthPathCharges.positiveCharge G x K := by
  classical
  obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hfree.1
  have haK : a.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.val.property, a.property⟩
  have hbK : b.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.val.property, b.property⟩
  have hend := Paper.HighGirthPathNeighborCounts.path_component_neighbor_counts G x K a b p hp hgraph
  by_cases hab : a = b
  · subst b
    have hn : p = SimpleGraph.Walk.nil := (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
    subst p
    have hsingle : Paper.HighGirthFreePaths.members G x K = {a.val.val} := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvU,hvComp⟩ := (Finset.mem_filter.mp hv).2
        let z : K := ⟨⟨v,hvU⟩,hvComp⟩
        have hz : z = a := by simpa using hcover z
        exact Finset.mem_singleton.mpr (congrArg (fun q : K => q.val.val) hz)
      · intro hv
        have heq := Finset.mem_singleton.mp hv
        simpa only [heq] using haK
    apply Paper.HighGirthSingletonCharge.singleton_attachment_charge G x hx K hfree.2 a.val.val hsingle
    rw [← (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).2 a.val.val hsingle]
    exact hcount
  · by_cases haA : a.val.val ∈ Paper.HighGirthAttachments.vertices G x
    · by_cases hbA : b.val.val ∈ Paper.HighGirthAttachments.vertices G x
      · obtain ⟨t,ht,hat⟩ := (Finset.mem_filter.mp haA).2
        obtain ⟨s,hs,hbs⟩ := (Finset.mem_filter.mp hbA).2
        have haU := (Finset.mem_filter.mp haK).2.1
        have hbU := (Finset.mem_filter.mp hbK).2.1
        have hatK : (a.val.val,t) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haU,ht⟩,hat⟩,haK⟩
        have hbsK : (b.val.val,s) ∈ Paper.HighGirthComponentAttachments.pairs G x K :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbU,hs⟩,hbs⟩,hbK⟩
        have hne : (a.val.val,t) ≠ (b.val.val,s) := by
          intro heq
          apply hab
          exact Subtype.ext (Subtype.ext (congrArg Prod.fst heq))
        have hsub : ({(a.val.val,t),(b.val.val,s)} : Finset (V × V)) ⊆
            Paper.HighGirthComponentAttachments.pairs G x K := by
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hatK
          · exact Finset.mem_singleton.mp hq ▸ hbsK
        have hc := Finset.card_le_card hsub
        have htwo : 2 ≤ (Paper.HighGirthComponentAttachments.pairs G x K).card := by simpa [hne] using hc
        have he := (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1
        change (Paper.HighGirthComponentAttachments.edges G x K).card ≤ 1 at hcount
        omega
      · exact Paper.HighGirthUnattachedEndpoint.unattached_endpoint_charge G x hx K hfree.2 b.val.val hbK hend.2.1 hbA
    · exact Paper.HighGirthUnattachedEndpoint.unattached_endpoint_charge G x hx K hfree.2 a.val.val haK hend.1 haA

end Paper.HighGirthOneAttachmentCharge

#print axioms Paper.HighGirthOneAttachmentCharge.one_attachment_charge
