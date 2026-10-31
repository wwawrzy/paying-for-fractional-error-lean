import Paper.TotalDomination.HighGirthNonfreeSize

namespace Paper.TotalDomination.HighGirthSetup

theorem nonfree_and_free_attachment_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (nonfreeAttachments G x identifier hfree).card +
      (∑ K ∈ freeComponents G x identifier hfree,
        (componentAttachmentPairs G x identifier hfree K).card) ≤ (attachmentPairs G x identifier hfree).card := by
  classical
    let F := freeComponents G x identifier hfree
    let P := F.biUnion (componentAttachmentPairs G x identifier hfree)
    let N := nonfreeVertices G x identifier hfree
    let Q := (attachmentPairs G x identifier hfree).filter (fun p => p.1 ∈ N)
    have himage : nonfreeAttachments G x identifier hfree = Q.image Prod.fst := by
      ext u
      constructor
      · intro hu
        obtain ⟨huA, huN⟩ := Finset.mem_inter.mp hu
        have huU := (Finset.mem_inter.mp huA).1
        obtain ⟨t,ht,hadj⟩ := (Paper.TotalDomination.mem_neighbors G).mp (Finset.mem_inter.mp huA).2
        have hp : (u, t) ∈ attachmentPairs G x identifier hfree :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huU, ht⟩, hadj⟩
        exact Finset.mem_image.mpr ⟨(u, t), Finset.mem_filter.mpr ⟨hp, huN⟩, rfl⟩
      · intro hu
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hpG, hpN⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpProd, hadj⟩ := Finset.mem_filter.mp hpG
        obtain ⟨huU, ht⟩ := Finset.mem_product.mp hpProd
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨huU,
          (Paper.TotalDomination.mem_neighbors G).mpr ⟨p.2,ht,hadj⟩⟩,hpN⟩
    have hA : (nonfreeAttachments G x identifier hfree).card ≤ Q.card := by
      rw [himage]
      exact Finset.card_image_le
    have hdis : (↑F : Set (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent).PairwiseDisjoint
        (componentAttachmentPairs G x identifier hfree) := by
      intro K hK J hJ hne
      apply Finset.disjoint_left.mpr
      intro p hpK hpJ
      obtain ⟨huK, hcK⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hpK).2).2
      obtain ⟨huJ, hcJ⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hpJ).2).2
      exact hne (hcK.symm.trans hcJ)
    have hsum : (∑ K ∈ F, (componentAttachmentPairs G x identifier hfree K).card) = P.card := by
      calc
        _ = ∑ K ∈ F, (componentAttachmentPairs G x identifier hfree K).card := rfl
        _ = P.card := (Finset.card_biUnion hdis).symm
    have hQP : Disjoint Q P := by
      apply Finset.disjoint_left.mpr
      intro p hpQ hpP
      have hpN : p.1 ∈ N := (Finset.mem_filter.mp hpQ).2
      obtain ⟨K, hK, hpK⟩ := Finset.mem_biUnion.mp hpP
      have huK : p.1 ∈ componentMembers G x identifier hfree K := (Finset.mem_filter.mp hpK).2
      have huF : p.1 ∈ freeVertices G x identifier hfree := Finset.mem_biUnion.mpr ⟨K, hK, huK⟩
      exact (Finset.mem_sdiff.mp hpN).2 huF
    have hsub : Q ∪ P ⊆ attachmentPairs G x identifier hfree := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · obtain ⟨K, _, hpK⟩ := Finset.mem_biUnion.mp hp
        exact (Finset.mem_filter.mp hpK).1
    change (nonfreeAttachments G x identifier hfree).card + (∑ K ∈ F, (componentAttachmentPairs G x identifier hfree K).card) ≤ _
    rw [hsum]
    calc
      _ ≤ Q.card + P.card := Nat.add_le_add_right hA _
      _ = (Q ∪ P).card := (Finset.card_union_of_disjoint hQP).symm
      _ ≤ (attachmentPairs G x identifier hfree).card := Finset.card_le_card hsub
      _ = (attachmentPairs G x identifier hfree).card := rfl

end Paper.TotalDomination.HighGirthSetup
