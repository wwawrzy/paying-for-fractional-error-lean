import Paper.Endpoints.Girth.HighGirthSplitAttachmentBudget
set_option maxHeartbeats 200000
namespace Paper.HighGirthRetainedSize

theorem retained_set_size_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (Paper.HighGirthRetainedSet.vertices G x).card +
      4 * (Paper.HighGirthComponentCounting.freeComponents G x).card +
      (Paper.HighGirthFreeAttachmentClasses.two G x).card ≤
      5 * Paper.HighGirthAttachments.count G x +
      4 * (Paper.HighGirthRounding.middle G x).card +
      (Paper.HighGirthFewAttachments.twoFamily G x).card := by
  classical
    let F := Paper.HighGirthComponentCounting.freeComponents G x
    let B2 := Paper.HighGirthFewAttachments.twoFamily G x
    let N := Paper.HighGirthNonfreeRegion.vertices G x
    let R := Paper.HighGirthRetainedSet.parts G x
    have hs := Paper.HighGirthRetainedSet.parts_spec G x
    have hF : ∀ K, K ∈ F ↔ Paper.HighGirthFreePaths.isFreePath G x K := by
      intro K
      simp [F,Paper.HighGirthComponentCounting.freeComponents,Paper.HighGirthComponentCounting.pathComponents,Paper.HighGirthFreePaths.isFreePath]
    have huniq : ∀ K J (u : V), u ∈ Paper.HighGirthFreePaths.members G x K →
        u ∈ Paper.HighGirthFreePaths.members G x J → K = J := by
      intro K J u huK huJ
      obtain ⟨hu,hK⟩ := (Finset.mem_filter.mp huK).2
      obtain ⟨hu',hJ⟩ := (Finset.mem_filter.mp huJ).2
      exact hK.symm.trans hJ
    have hcover : Paper.HighGirthRetainedSet.vertices G x ⊆ N ∪ F.biUnion R := by
      intro u hu
      obtain ⟨K,_,huR⟩ := Finset.mem_biUnion.mp hu
      have huK : u ∈ Paper.HighGirthFreePaths.members G x K := (hs K).2.1 huR
      by_cases hf : Paper.HighGirthFreePaths.isFreePath G x K
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨K,(hF K).mpr hf,huR⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        obtain ⟨huU,_⟩ := (Finset.mem_filter.mp huK).2
        refine ⟨huU,?_⟩
        intro huFree
        obtain ⟨J,hJF,huJ⟩ := Finset.mem_biUnion.mp huFree
        have he := huniq J K u huJ huK
        have hfJ := (hF J).mp hJF
        exact hf (by simpa only [he] using hfJ)
    have hcard : (Paper.HighGirthRetainedSet.vertices G x).card ≤ N.card + ∑ K ∈ F, (R K).card := by
      calc
        _ ≤ (N ∪ F.biUnion R).card := Finset.card_le_card hcover
        _ ≤ N.card + (F.biUnion R).card := Finset.card_union_le _ _
        _ ≤ N.card + ∑ K ∈ F, (R K).card := Nat.add_le_add_left Finset.card_biUnion_le _
    have hBsub : B2 ⊆ F := by
      intro K hK
      have hf : Paper.HighGirthFreePaths.isFreePath G x K := (Finset.mem_filter.mp hK).2.1
      exact (hF K).mpr hf
    have hfilter : Finset.filter (fun K => K ∈ B2) F = B2 := by
      ext K
      constructor
      · intro hK
        exact (Finset.mem_filter.mp hK).2
      · intro hK
        exact Finset.mem_filter.mpr ⟨hBsub hK,hK⟩
    have hb : (∑ K ∈ F, if K ∈ B2 then 1 else 0) = B2.card := by
      simpa [hfilter] using (Finset.card_filter (fun K => K ∈ B2) F).symm
    have h2 : (∑ K ∈ F, if Paper.HighGirthComponentAttachments.count G x K = 2 then 1 else 0) =
        (Paper.HighGirthFreeAttachmentClasses.two G x).card := by
      simp [Paper.HighGirthFreeAttachmentClasses.two,F]
    have hpoint : ∀ K ∈ F, (R K).card + 4 +
        (if Paper.HighGirthComponentAttachments.count G x K = 2 then 1 else 0) ≤
        5 * Paper.HighGirthComponentAttachments.count G x K + (if K ∈ B2 then 1 else 0) := by
      intro K hK
      have hbound := (hs K).2.2.2.2.2 ((hF K).mp hK)
      have hbase : (R K).card + 4 ≤ 5 * Paper.HighGirthComponentAttachments.count G x K := hbound.1
      by_cases hc : Paper.HighGirthComponentAttachments.count G x K = 2
      · by_cases he : K ∈ B2
        · simp only [hc,he,ite_true]
          omega
        · have hsmall : (R K).card ≤ 5 := hbound.2 hc he
          simp only [hc,he,ite_true,ite_false]
          omega
      · by_cases he : K ∈ B2
        · simp only [hc,he,ite_false,ite_true]
          omega
        · simp only [hc,he,ite_false]
          exact hbase
    have hsum := Finset.sum_le_sum hpoint
    have hsum' : (∑ K ∈ F, (R K).card) + 4 * F.card +
        (Paper.HighGirthFreeAttachmentClasses.two G x).card ≤
        5 * (∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K) + B2.card := by
      simpa only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,h2,hb,Nat.mul_comm] using hsum
    have hN := Paper.HighGirthNonfreeSize.nonfree_region_size_bound G x
    have hbudget := Paper.HighGirthSplitAttachmentBudget.nonfree_and_free_attachment_budget G x
    change (Paper.HighGirthRetainedSet.vertices G x).card + 4 * F.card +
        (Paper.HighGirthFreeAttachmentClasses.two G x).card ≤
        5 * Paper.HighGirthAttachments.count G x + 4 * (Paper.HighGirthRounding.middle G x).card + B2.card
    change N.card ≤ 5 * (Paper.HighGirthNonfreeRegion.attachments G x).card + 4 * (Paper.HighGirthRounding.middle G x).card at hN
    change (Paper.HighGirthNonfreeRegion.attachments G x).card + (∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K) ≤ Paper.HighGirthAttachments.count G x at hbudget
    omega

end Paper.HighGirthRetainedSize

#print axioms Paper.HighGirthRetainedSize.retained_set_size_bound
