import Paper.Endpoints.Girth.HighGirthAttachmentVertices

/-! Actual two-attachment half-slack when the two attached vertices are
branches. No claim here derives branch membership from distance five. -/
namespace Paper.HighGirthTwoBranchAttachments

theorem half_slack
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K)
    (hcount : HighGirthComponentAttachments.count G x K ≤ 2)
    (a b : V) (haK : a ∈ HighGirthFreePaths.members G x K)
    (hbK : b ∈ HighGirthFreePaths.members G x K) (hab : a ≠ b)
    (haA : a ∈ HighGirthAttachments.vertices G x)
    (hbA : b ∈ HighGirthAttachments.vertices G x)
    (haB : a ∈ HighGirthTransformation.branches G)
    (hbB : b ∈ HighGirthTransformation.branches G) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K := by
  apply HighGirthBranchPathCharge.half_slack_of_branch_attachments G x hx K hfree hcount a b haK hbK hab haA hbA
  intro u huK huA
  rcases HighGirthAttachmentVertices.attachment_vertices_exhausted G x K hcount a b haK hbK hab haA hbA u huK huA with h | h
  · simpa only [h] using haB
  · simpa only [h] using hbB

end Paper.HighGirthTwoBranchAttachments

#print axioms Paper.HighGirthTwoBranchAttachments.half_slack
