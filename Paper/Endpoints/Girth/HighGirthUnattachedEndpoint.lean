import Paper.Endpoints.Girth.HighGirthExcessPacking
set_option maxHeartbeats 200000
namespace Paper.HighGirthUnattachedEndpoint

theorem unattached_endpoint_charge
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K)
    (b : V) (hbK : b ∈ Paper.HighGirthFreePaths.members G x K)
    (hend : (G.neighborFinset b ∩ Paper.HighGirthFreePaths.members G x K).card ≤ 1)
    (hbA : b ∉ Paper.HighGirthAttachments.vertices G x) :
    (1 : Real) / 2 ≤ Paper.HighGirthPathCharges.positiveCharge G x K := by
  classical
    let S := Paper.SevenFoundation.closed G b
    let P := S ∩ Paper.HighGirthRounding.positive G x
    let N := G.neighborFinset b ∩ Paper.HighGirthFreePaths.members G x K
    obtain ⟨hbU,hbComp⟩ := (Finset.mem_filter.mp hbK).2
    have hbR0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hbU).1).1
    have hbPos := Paper.HighGirthFreeEndpoints.free_endpoint_positive G x K hfree b hbK hend
    have hsub : S \ P ⊆ N := by
      intro z hz
      obtain ⟨hzS,hzP⟩ := Finset.mem_sdiff.mp hz
      have hzNotPos : z ∉ Paper.HighGirthRounding.positive G x := fun h => hzP (Finset.mem_inter.mpr ⟨hzS,h⟩)
      rcases (Paper.SevenFoundation.mem_closed G z b).mp hzS with heq | hbz
      · exact False.elim (hzNotPos (by simpa only [heq] using hbPos))
      · by_cases hzK : z ∈ Paper.HighGirthFreePaths.members G x K
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b z).mpr hbz,hzK⟩
        · have hext := Paper.HighGirthFreeExternal.free_external_neighbors G x K hfree b hbK z hzK hbz
          have hz0 : z ∉ Paper.HighGirthTransformation.demands G := by
            intro hz0
            have ht := hext.2.2.1 hz0
            exact hbA (Finset.mem_filter.mpr ⟨hbU,⟨z,ht,hbz⟩⟩)
          exact False.elim (hzNotPos (hext.2.2.2 hz0).1)
    have hsumP : (∑ z ∈ P, x z) ≤ Paper.HighGirthPathCharges.positiveCharge G x K := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        obtain ⟨hzS,hzPos⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨hzPos,Finset.mem_biUnion.mpr ⟨b,hbK,hzS⟩⟩
      · intro z hz hn
        exact hx.1 z
    have hsumN : (∑ z ∈ N, x z) ≤ (1 : Real) / 2 := by
      calc
        _ ≤ ∑ _z ∈ N, (1 : Real) / 2 := by
          apply Finset.sum_le_sum
          intro z hz
          obtain ⟨hzU,hzComp⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
          exact (Paper.HighGirthFreeCoordinates.residual_threshold_coordinates G x).1 z hzU
        _ = (N.card : Real) * ((1 : Real) / 2) := by simp
        _ ≤ (1 : Real) / 2 := by
          have hc : (N.card : Real) ≤ 1 := by exact_mod_cast hend
          linarith
    have hsumRest : (∑ z ∈ S \ P, x z) ≤ ∑ z ∈ N, x z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz hn => hx.1 z)
    have hsplit : (∑ z ∈ S \ P, x z) + (∑ z ∈ P, x z) = ∑ z ∈ S, x z :=
      Finset.sum_sdiff Finset.inter_subset_left
    have hrow := hx.2.2 b hbR0
    change 1 ≤ ∑ z ∈ Paper.SevenFoundation.closed G b ∩ Paper.HighGirthTransformation.zone G, x z at hrow
    rw [Finset.inter_eq_left.mpr ((Paper.HighGirthRestriction.restriction_feasible G).1 b hbR0)] at hrow
    change 1 ≤ ∑ z ∈ S, x z at hrow
    linarith

end Paper.HighGirthUnattachedEndpoint

#print axioms Paper.HighGirthUnattachedEndpoint.unattached_endpoint_charge
