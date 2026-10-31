import Paper.Endpoints.Girth.HighGirthOneAttachmentCharge

/-! The full one-attachment subcase of fv:hg:half, using actual component
edges and original auxiliary feasibility. The two-attachment case remains open. -/
namespace Paper.HighGirthOneAttachment

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

theorem row_excess_nonnegative
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    0 ≤ HighGirthPathCharges.rowExcess G x K := by
  classical
  apply Finset.sum_nonneg
  intro r hr
  obtain ⟨hrU,hrComp⟩ := (Finset.mem_filter.mp hr).2
  have hr0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hrU).1).1
  have hrow := hx.2.2 r hr0
  change 1 ≤ ∑ v ∈ SevenFoundation.closed G r ∩ HighGirthTransformation.zone G, x v at hrow
  rw [Finset.inter_eq_left.mpr ((HighGirthRestriction.restriction_feasible G).1 r hr0)] at hrow
  exact sub_nonneg.mpr hrow

theorem half_slack
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K)
    (hcount : HighGirthComponentAttachments.count G x K ≤ 1) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K := by
  have hq := HighGirthOneAttachmentCharge.one_attachment_charge G x hx K hfree hcount
  have ho := row_excess_nonnegative G x hx K
  linarith

theorem count_one_attachment_paths
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (family : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfamily : ∀ K ∈ family, HighGirthFreePaths.isFreePath G x K ∧
      HighGirthComponentAttachments.count G x K = 1) :
    (family.card : Real) ≤ 4 * HighGirthRounding.penalty G x + 2 * HighGirthRounding.oversupply G x := by
  apply HighGirthHalfCounting.count_of_half_slack G x hx family
  intro K hK
  obtain ⟨hf,hc⟩ := hfamily K hK
  exact half_slack G x hx K hf (by omega)

end Paper.HighGirthOneAttachment

#print axioms Paper.HighGirthOneAttachment.row_excess_nonnegative
#print axioms Paper.HighGirthOneAttachment.half_slack
#print axioms Paper.HighGirthOneAttachment.count_one_attachment_paths
