import Paper.TotalDomination.HighGirthSplitAttachmentBudget

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem free_bad_correction_sum :
    (∑ C ∈ freeComponents G x identifier hfree, badCorrection G x identifier hfree C) =
      2*(badComponents G x identifier hfree).card := by
  classical
  have heq : (freeComponents G x identifier hfree).filter (Bad G x identifier hfree) = badComponents G x identifier hfree := by
    ext C
    constructor
    · intro hC
      exact Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]),(Finset.mem_filter.mp hC).2⟩
    · intro hC
      have hB := (Finset.mem_filter.mp hC).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]),hB.2.1,hB.1⟩,hB⟩
  unfold badCorrection
  rw [← Finset.sum_filter,heq]
  simp [Nat.mul_comm]

theorem retained_size_bound : (retainedVertices G x identifier hfree).card +
    8*(freeComponents G x identifier hfree).card ≤
    7*(attachmentEdges G x identifier hfree).card + 6*(served G (I G x identifier hfree)).card +
      2*(badComponents G x identifier hfree).card := by
  classical
  let F := freeComponents G x identifier hfree
  let N := nonfreeVertices G x identifier hfree
  let R := retainedParts G x identifier hfree
  have hs := retainedParts_spec G x identifier hfree
  have hF : ∀ C, C ∈ F ↔ isFreePathComponent G x identifier hfree C := by
    intro C
    simp only [F,freeComponents,Finset.mem_filter,Finset.mem_univ,true_and]
  have hcover : retainedVertices G x identifier hfree ⊆ N ∪ F.biUnion R := by
    intro u hu
    obtain ⟨C,hC,huR⟩ := Finset.mem_biUnion.mp hu
    have huC := (hs C).2.1 huR
    by_cases hf : isFreePathComponent G x identifier hfree C
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C,(hF C).mpr hf,huR⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨component_subset_core G x identifier hfree C huC,?_⟩
      intro huF
      obtain ⟨D,hD,huD⟩ := Finset.mem_biUnion.mp huF
      have he := component_member_unique G x identifier hfree D C huD huC
      have hfD := (hF D).mp hD
      exact hf (by simpa only [he] using hfD)
  have hcard : (retainedVertices G x identifier hfree).card ≤ N.card + ∑ C ∈ F, (R C).card := by
    calc
      _ ≤ (N ∪ F.biUnion R).card := Finset.card_le_card hcover
      _ ≤ N.card+(F.biUnion R).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _
  have hpoint : ∀ C ∈ F, (R C).card+8 ≤ 7*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C :=
    fun C hC => (hs C).2.2.2.2.2 ((hF C).mp hC)
  have hsum := Finset.sum_le_sum hpoint
  have hsum' : (∑ C ∈ F, (R C).card)+8*F.card ≤
      7*(∑ C ∈ F, (componentAttachmentPairs G x identifier hfree C).card) + 2*(badComponents G x identifier hfree).card := by
    simpa only [F,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,
      free_bad_correction_sum,Nat.mul_comm] using hsum
  have hN := nonfree_size_bound G x identifier hfree
  have hbudget := nonfree_and_free_attachment_budget G x identifier hfree
  rw [attachment_edges_card G x identifier hfree]
  change (retainedVertices G x identifier hfree).card+8*F.card ≤ _
  change N.card ≤ 7*(nonfreeAttachments G x identifier hfree).card+6*(served G (I G x identifier hfree)).card at hN
  change (nonfreeAttachments G x identifier hfree).card +
    (∑ C ∈ F, (componentAttachmentPairs G x identifier hfree C).card) ≤ (attachmentPairs G x identifier hfree).card at hbudget
  omega

end Paper.TotalDomination.HighGirthSetup
