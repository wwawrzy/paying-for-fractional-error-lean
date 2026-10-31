import Paper.Endpoints.Girth.HighGirthDistanceFiveBranches

/-! The original two families from fv:hg:half on genuine components of G[U].
Attachment counts are actual unordered original graph edge counts. Distance
five is measured in the actual component graph, not in G. -/
namespace Paper.HighGirthFewAttachments

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def oneFamily : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact Finset.univ.filter (fun K => HighGirthFreePaths.isFreePath G x K ∧
    HighGirthComponentAttachments.count G x K = 1)

noncomputable def twoFamily : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact Finset.univ.filter (fun K => HighGirthFreePaths.isFreePath G x K ∧
    HighGirthComponentAttachments.count G x K = 2 ∧
    ∃ a b : K, a.val.val ∈ HighGirthAttachments.vertices G x ∧
      b.val.val ∈ HighGirthAttachments.vertices G x ∧ K.toSimpleGraph.dist a b = 5)

noncomputable def families : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact oneFamily G x ∪ twoFamily G x

theorem two_attachment_half_slack
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K)
    (hcount : HighGirthComponentAttachments.count G x K = 2)
    (a b : K) (haA : a.val.val ∈ HighGirthAttachments.vertices G x)
    (hbA : b.val.val ∈ HighGirthAttachments.vertices G x)
    (hdist : K.toSimpleGraph.dist a b = 5) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K := by
  classical
  have haK : a.val.val ∈ HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
  have hbK : b.val.val ∈ HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,b.val.property,b.property⟩
  have hab : a.val.val ≠ b.val.val := by
    intro h
    have he : a = b := Subtype.ext (Subtype.ext h)
    subst b
    simpa using hdist
  obtain ⟨haB,hbB⟩ := HighGirthDistanceFiveBranches.distance_five_attachments_are_branches G x K hfree hcount a b haA hbA hdist
  exact HighGirthTwoBranchAttachments.half_slack G x hx K hfree (by omega) a.val.val b.val.val haK hbK hab haA hbA haB hbB

theorem families_disjoint : Disjoint (oneFamily G x) (twoFamily G x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro K h1 h2
  have hc1 := (Finset.mem_filter.mp h1).2.2
  have hc2 := (Finset.mem_filter.mp h2).2.2.1
  omega

theorem half_slack
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hK : K ∈ families G x) :
    (1 : Real) / 2 ≤ HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K := by
  classical
  change K ∈ oneFamily G x ∪ twoFamily G x at hK
  rcases Finset.mem_union.mp hK with h1 | h2
  · obtain ⟨hf,hc⟩ := (Finset.mem_filter.mp h1).2
    exact HighGirthOneAttachment.half_slack G x hx K hf (by omega)
  · obtain ⟨hf,hc,a,b,ha,hb,hd⟩ := (Finset.mem_filter.mp h2).2
    exact two_attachment_half_slack G x hx K hf hc a b ha hb hd

theorem count_bound
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x) :
    ((oneFamily G x).card : Real) + ((twoFamily G x).card : Real) ≤
      4 * HighGirthRounding.penalty G x + 2 * HighGirthRounding.oversupply G x := by
  classical
  have h := HighGirthHalfCounting.count_of_half_slack G x hx (oneFamily G x ∪ twoFamily G x)
    (fun K hK => half_slack G x hx K hK)
  rw [Finset.card_union_of_disjoint (families_disjoint G x),Nat.cast_add] at h
  exact h

theorem few_attachment_endpoint
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x) :
    (∀ K ∈ families G x, (1 : Real) / 2 ≤
      HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K) ∧
    ((oneFamily G x).card : Real) + ((twoFamily G x).card : Real) ≤
      4 * HighGirthRounding.penalty G x + 2 * HighGirthRounding.oversupply G x :=
  ⟨fun K hK => half_slack G x hx K hK,count_bound G x hx⟩

end Paper.HighGirthFewAttachments

#print axioms Paper.HighGirthFewAttachments.families
#print axioms Paper.HighGirthFewAttachments.oneFamily
#print axioms Paper.HighGirthFewAttachments.twoFamily
#print axioms Paper.HighGirthFewAttachments.two_attachment_half_slack
#print axioms Paper.HighGirthFewAttachments.families_disjoint
#print axioms Paper.HighGirthFewAttachments.half_slack
#print axioms Paper.HighGirthFewAttachments.count_bound
#print axioms Paper.HighGirthFewAttachments.few_attachment_endpoint
