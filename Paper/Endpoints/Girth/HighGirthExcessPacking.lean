import Paper.Endpoints.Girth.HighGirthChargePacking
set_option maxHeartbeats 200000
namespace Paper.HighGirthExcessPacking

theorem component_row_excess_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (family : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    (∑ K ∈ family, Paper.HighGirthPathCharges.rowExcess G x K) ≤
      Paper.HighGirthRounding.oversupply G x := by
  classical
  let omegaRow := fun r => (∑ v ∈ Paper.SevenFoundation.closed G r, x v) - 1
  have hdis : (↑family : Set (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent).Pairwise
      (fun K J => Disjoint (Paper.HighGirthFreePaths.members G x K) (Paper.HighGirthFreePaths.members G x J)) := by
    intro K hK J hJ hne
    apply Finset.disjoint_left.mpr
    intro u huK huJ
    obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
    obtain ⟨huU',huComp'⟩ := (Finset.mem_filter.mp huJ).2
    exact hne (huComp.symm.trans huComp')
  have hsub : family.biUnion (Paper.HighGirthFreePaths.members G x) ⊆ Paper.HighGirthRounding.residual G x := by
    intro r hr
    obtain ⟨K,hK,hrK⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨hrU,hrComp⟩ := (Finset.mem_filter.mp hrK).2
    exact (Finset.mem_sdiff.mp hrU).1
  have hrow : ∀ r ∈ Paper.HighGirthRounding.residual G x, 0 ≤ omegaRow r := by
    intro r hr
    have hr0 := (Finset.mem_sdiff.mp hr).1
    have hh := hx.2.2 r hr0
    change 1 ≤ ∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G, x v at hh
    rw [Finset.inter_eq_left.mpr ((Paper.HighGirthRestriction.restriction_feasible G).1 r hr0)] at hh
    exact sub_nonneg.mpr hh
  change (∑ K ∈ family, ∑ r ∈ Paper.HighGirthFreePaths.members G x K, omegaRow r) ≤
    ∑ r ∈ Paper.HighGirthRounding.residual G x, omegaRow r
  calc
    _ = ∑ r ∈ family.biUnion (Paper.HighGirthFreePaths.members G x), omegaRow r := (Finset.sum_biUnion hdis).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r hr hn => hrow r hr)

end Paper.HighGirthExcessPacking

#print axioms Paper.HighGirthExcessPacking.component_row_excess_bound
