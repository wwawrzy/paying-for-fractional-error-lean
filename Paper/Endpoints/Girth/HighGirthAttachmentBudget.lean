import Paper.Endpoints.Girth.HighGirthPathComponentCount
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentBudget

theorem component_attachment_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (family : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    (∑ K ∈ family, Paper.HighGirthComponentAttachments.count G x K) ≤
      Paper.HighGirthAttachments.count G x := by
  classical
    have hdis : (↑family : Set (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent).PairwiseDisjoint
        (Paper.HighGirthComponentAttachments.pairs G x) := by
      intro K hK J hJ hne
      apply Finset.disjoint_left.mpr
      intro p hpK hpJ
      have hmK := (Finset.mem_filter.mp hpK).2
      have hmJ := (Finset.mem_filter.mp hpJ).2
      obtain ⟨huK,hcK⟩ := (Finset.mem_filter.mp hmK).2
      obtain ⟨huJ,hcJ⟩ := (Finset.mem_filter.mp hmJ).2
      exact hne (hcK.symm.trans hcJ)
    have hsub : family.biUnion (Paper.HighGirthComponentAttachments.pairs G x) ⊆ Paper.HighGirthAttachments.pairs G x := by
      intro p hp
      obtain ⟨K,hK,hpK⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp hpK).1
    calc
      _ = ∑ K ∈ family, (Paper.HighGirthComponentAttachments.pairs G x K).card := by
        apply Finset.sum_congr rfl
        intro K hK
        exact (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1
      _ = (family.biUnion (Paper.HighGirthComponentAttachments.pairs G x)).card := (Finset.card_biUnion hdis).symm
      _ ≤ (Paper.HighGirthAttachments.pairs G x).card := Finset.card_le_card hsub
      _ = _ := rfl

end Paper.HighGirthAttachmentBudget

#print axioms Paper.HighGirthAttachmentBudget.component_attachment_budget
