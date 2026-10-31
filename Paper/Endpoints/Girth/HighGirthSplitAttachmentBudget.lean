import Paper.Endpoints.Girth.HighGirthNonfreeSize
set_option maxHeartbeats 200000
namespace Paper.HighGirthSplitAttachmentBudget

theorem nonfree_and_free_attachment_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (Paper.HighGirthNonfreeRegion.attachments G x).card +
      (∑ K ∈ Paper.HighGirthComponentCounting.freeComponents G x,
        Paper.HighGirthComponentAttachments.count G x K) ≤ Paper.HighGirthAttachments.count G x := by
  classical
    let F := Paper.HighGirthComponentCounting.freeComponents G x
    let P := F.biUnion (Paper.HighGirthComponentAttachments.pairs G x)
    let N := Paper.HighGirthNonfreeRegion.vertices G x
    let Q := (Paper.HighGirthAttachments.pairs G x).filter (fun p => p.1 ∈ N)
    have himage : Paper.HighGirthNonfreeRegion.attachments G x = Q.image Prod.fst := by
      ext u
      constructor
      · intro hu
        obtain ⟨huA, huN⟩ := Finset.mem_inter.mp hu
        obtain ⟨huU, t, ht, hadj⟩ := Finset.mem_filter.mp huA
        have hp : (u, t) ∈ Paper.HighGirthAttachments.pairs G x :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huU, ht⟩, hadj⟩
        exact Finset.mem_image.mpr ⟨(u, t), Finset.mem_filter.mpr ⟨hp, huN⟩, rfl⟩
      · intro hu
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hpG, hpN⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpProd, hadj⟩ := Finset.mem_filter.mp hpG
        obtain ⟨huU, ht⟩ := Finset.mem_product.mp hpProd
        exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨huU, ⟨p.2, ht, hadj⟩⟩, hpN⟩
    have hA : (Paper.HighGirthNonfreeRegion.attachments G x).card ≤ Q.card := by
      rw [himage]
      exact Finset.card_image_le
    have hdis : (↑F : Set (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent).PairwiseDisjoint
        (Paper.HighGirthComponentAttachments.pairs G x) := by
      intro K hK J hJ hne
      apply Finset.disjoint_left.mpr
      intro p hpK hpJ
      obtain ⟨huK, hcK⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hpK).2).2
      obtain ⟨huJ, hcJ⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hpJ).2).2
      exact hne (hcK.symm.trans hcJ)
    have hsum : (∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K) = P.card := by
      calc
        _ = ∑ K ∈ F, (Paper.HighGirthComponentAttachments.pairs G x K).card := by
          apply Finset.sum_congr rfl
          intro K hK
          exact (Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1
        _ = P.card := (Finset.card_biUnion hdis).symm
    have hQP : Disjoint Q P := by
      apply Finset.disjoint_left.mpr
      intro p hpQ hpP
      have hpN : p.1 ∈ N := (Finset.mem_filter.mp hpQ).2
      obtain ⟨K, hK, hpK⟩ := Finset.mem_biUnion.mp hpP
      have huK : p.1 ∈ Paper.HighGirthFreePaths.members G x K := (Finset.mem_filter.mp hpK).2
      have huF : p.1 ∈ Paper.HighGirthNonfreeRegion.freeVertices G x := Finset.mem_biUnion.mpr ⟨K, hK, huK⟩
      exact (Finset.mem_sdiff.mp hpN).2 huF
    have hsub : Q ∪ P ⊆ Paper.HighGirthAttachments.pairs G x := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · obtain ⟨K, _, hpK⟩ := Finset.mem_biUnion.mp hp
        exact (Finset.mem_filter.mp hpK).1
    change (Paper.HighGirthNonfreeRegion.attachments G x).card + (∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K) ≤ _
    rw [hsum]
    calc
      _ ≤ Q.card + P.card := Nat.add_le_add_right hA _
      _ = (Q ∪ P).card := (Finset.card_union_of_disjoint hQP).symm
      _ ≤ (Paper.HighGirthAttachments.pairs G x).card := Finset.card_le_card hsub
      _ = Paper.HighGirthAttachments.count G x := rfl

end Paper.HighGirthSplitAttachmentBudget

#print axioms Paper.HighGirthSplitAttachmentBudget.nonfree_and_free_attachment_budget
