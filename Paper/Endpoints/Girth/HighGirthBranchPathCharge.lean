import Paper.Endpoints.Girth.HighGirthAttachmentFibers

/-! A genuine two-attachment graph subcase. The premise that all attachment
vertices in K are branches is explicit. Deriving it from source distance five
is still required before certifying fv:hg:half. -/
namespace Paper.HighGirthBranchPathCharge

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

theorem charge_of_branch_attachments
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K)
    (hcount : HighGirthComponentAttachments.count G x K ≤ 2)
    (a b : V) (haK : a ∈ HighGirthFreePaths.members G x K)
    (hbK : b ∈ HighGirthFreePaths.members G x K) (hab : a ≠ b)
    (haA : a ∈ HighGirthAttachments.vertices G x)
    (hbA : b ∈ HighGirthAttachments.vertices G x)
    (hbranches : ∀ u ∈ HighGirthFreePaths.members G x K,
      u ∈ HighGirthAttachments.vertices G x → u ∈ HighGirthTransformation.branches G) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K := by
  classical
  obtain ⟨c,d,p,hp,hcover,hgraph⟩ := hfree.1
  have hcK : c.val.val ∈ HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,c.val.property,c.property⟩
  have hend := (HighGirthPathNeighborCounts.path_component_neighbor_counts G x K c d p hp hgraph).1
  have hcA : c.val.val ∉ HighGirthAttachments.vertices G x := by
    intro hcA
    have hcB := hbranches _ hcK hcA
    have hT : (G.neighborFinset c.val.val ∩ HighGirthAttachments.connectors G x).card ≤ 1 := by
      by_cases hca : c.val.val = a
      · exact HighGirthAttachmentFibers.connector_fiber_at_most_one G x K hcount _ b hcK hbK (by simpa only [hca] using hab) hbA
      · exact HighGirthAttachmentFibers.connector_fiber_at_most_one G x K hcount _ a hcK haK hca haA
    have hinner := HighGirthBranchAttachment.branch_with_one_connector_is_inner G x K hfree.2 _ hcK hcB hT
    omega
  exact HighGirthUnattachedEndpoint.unattached_endpoint_charge G x hx K hfree.2 _ hcK hend hcA

theorem half_slack_of_branch_attachments
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K)
    (hcount : HighGirthComponentAttachments.count G x K ≤ 2)
    (a b : V) (haK : a ∈ HighGirthFreePaths.members G x K)
    (hbK : b ∈ HighGirthFreePaths.members G x K) (hab : a ≠ b)
    (haA : a ∈ HighGirthAttachments.vertices G x)
    (hbA : b ∈ HighGirthAttachments.vertices G x)
    (hbranches : ∀ u ∈ HighGirthFreePaths.members G x K,
      u ∈ HighGirthAttachments.vertices G x → u ∈ HighGirthTransformation.branches G) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K := by
  have hq := charge_of_branch_attachments G x hx K hfree hcount a b haK hbK hab haA hbA hbranches
  have ho := HighGirthOneAttachment.row_excess_nonnegative G x hx K
  linarith

end Paper.HighGirthBranchPathCharge

#print axioms Paper.HighGirthBranchPathCharge.charge_of_branch_attachments
#print axioms Paper.HighGirthBranchPathCharge.half_slack_of_branch_attachments
