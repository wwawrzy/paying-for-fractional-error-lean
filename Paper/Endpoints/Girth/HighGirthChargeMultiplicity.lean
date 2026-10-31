import Paper.Endpoints.Girth.HighGirthPathCharges
set_option maxHeartbeats 200000
namespace Paper.HighGirthChargeMultiplicity

theorem positive_component_multiplicity
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (family : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (v : V) (hv : v ∈ Paper.HighGirthRounding.positive G x) :
    (Paper.HighGirthPathCharges.incidentComponents G x family v).card ≤ Paper.HighGirthRounding.hits G x v ∧
    (Paper.HighGirthPathCharges.incidentComponents G x family v).card ≤ 2 := by
  classical
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    let I := Paper.HighGirthPathCharges.incidentComponents G x family v
    have hex : ∀ K ∈ I, ∃ u ∈ Paper.HighGirthFreePaths.members G x K, v ∈ Paper.SevenFoundation.closed G u := by
      intro K hK
      have hcover := (Finset.mem_filter.mp hK).2
      exact Finset.mem_biUnion.mp hcover
    let f : H.ConnectedComponent → V := fun K =>
      if hK : K ∈ I then Classical.choose (hex K hK) else v
    have hf : ∀ K ∈ I, f K ∈ Paper.HighGirthFreePaths.members G x K ∧ v ∈ Paper.SevenFoundation.closed G (f K) := by
      intro K hK
      simpa only [f,dif_pos hK] using Classical.choose_spec (hex K hK)
    have hmaps : Set.MapsTo f (↑I : Set H.ConnectedComponent)
        (↑(Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x) : Set V) := by
      intro K hK
      obtain ⟨hmem,hvu⟩ := hf K hK
      obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp hmem).2
      exact Finset.mem_inter.mpr ⟨(Paper.SevenFoundation.closed_symm G v (f K)).mp hvu,
        (Finset.mem_sdiff.mp huU).1⟩
    have hinj : Set.InjOn f (↑I : Set H.ConnectedComponent) := by
      intro K hK J hJ heq
      obtain ⟨hKU,hKComp⟩ := (Finset.mem_filter.mp (hf K hK).1).2
      obtain ⟨hJU,hJComp⟩ := (Finset.mem_filter.mp (hf J hJ).1).2
      have hs : (⟨f K,hKU⟩ : {u // u ∈ U}) = ⟨f J,hJU⟩ := Subtype.ext heq
      exact hKComp.symm.trans ((congrArg H.connectedComponentMk hs).trans hJComp)
    have hc : I.card ≤ Paper.HighGirthRounding.hits G x v :=
      Finset.card_le_card_of_injOn f hmaps hinj
    have hvO := (Finset.mem_filter.mp hv).1
    have hvGap := (Finset.mem_filter.mp hv).2
    have hvZ := (Finset.mem_sdiff.mp hvO).1
    have hcost := (Paper.HighGirthCostBounds.candidate_cost_bounds G v hvZ).2.1
    have hh : Paper.HighGirthRounding.hits G x v ≤ 2 := by omega
    exact ⟨hc,hc.trans hh⟩

end Paper.HighGirthChargeMultiplicity

#print axioms Paper.HighGirthChargeMultiplicity.positive_component_multiplicity
