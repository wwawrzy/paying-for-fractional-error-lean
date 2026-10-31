import Paper.Endpoints.Girth.HighGirthFreeAttachmentClasses
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeClassBounds

theorem free_attachment_class_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    3 * (Paper.HighGirthComponentCounting.freeComponents G x).card ≤
      Paper.HighGirthAttachments.count G x +
      2 * (Paper.HighGirthFreeAttachmentClasses.one G x).card +
      (Paper.HighGirthFreeAttachmentClasses.two G x).card ∧
    (Paper.HighGirthFreeAttachmentClasses.one G x).card +
      2 * (Paper.HighGirthFreeAttachmentClasses.two G x).card ≤
      Paper.HighGirthAttachments.count G x := by
  classical
  let F := Paper.HighGirthComponentCounting.freeComponents G x
  have h1 : (∑ K ∈ F, if Paper.HighGirthComponentAttachments.count G x K = 1 then 1 else 0) =
      (Paper.HighGirthFreeAttachmentClasses.one G x).card := by
    simp [Paper.HighGirthFreeAttachmentClasses.one,F]
  have h2 : (∑ K ∈ F, if Paper.HighGirthComponentAttachments.count G x K = 2 then 1 else 0) =
      (Paper.HighGirthFreeAttachmentClasses.two G x).card := by
    simp [Paper.HighGirthFreeAttachmentClasses.two,F]
  have ht : ∀ K ∈ F, 3 ≤ Paper.HighGirthComponentAttachments.count G x K +
      2 * (if Paper.HighGirthComponentAttachments.count G x K = 1 then 1 else 0) +
      (if Paper.HighGirthComponentAttachments.count G x K = 2 then 1 else 0) := by
    intro K hK
    have hp := Paper.HighGirthFreeAttachmentClasses.attachment_positive G x K hK
    split_ifs <;> omega
  have hb : ∀ K ∈ F, (if Paper.HighGirthComponentAttachments.count G x K = 1 then 1 else 0) +
      2 * (if Paper.HighGirthComponentAttachments.count G x K = 2 then 1 else 0) ≤
      Paper.HighGirthComponentAttachments.count G x K := by
    intro K hK
    split_ifs <;> omega
  have hsumt := Finset.sum_le_sum ht
  have hsumb := Finset.sum_le_sum hb
  have hthree : 3 * F.card ≤ (∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K) +
      2 * (Paper.HighGirthFreeAttachmentClasses.one G x).card +
      (Paper.HighGirthFreeAttachmentClasses.two G x).card := by
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,h1,h2,Nat.mul_comm] using hsumt
  have hsmall : (Paper.HighGirthFreeAttachmentClasses.one G x).card +
      2 * (Paper.HighGirthFreeAttachmentClasses.two G x).card ≤
      ∑ K ∈ F, Paper.HighGirthComponentAttachments.count G x K := by
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,h1,h2,Nat.mul_comm] using hsumb
  have hbudget := Paper.HighGirthAttachmentBudget.component_attachment_budget G x F
  constructor
  · change 3 * F.card ≤ _
    omega
  · omega

end Paper.HighGirthFreeClassBounds

#print axioms Paper.HighGirthFreeClassBounds.free_attachment_class_bounds
