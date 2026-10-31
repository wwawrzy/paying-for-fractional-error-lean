import Paper.Endpoints.Girth.HighGirthComponentCounting
set_option maxHeartbeats 200000
namespace Paper.HighGirthMiddleMultiplicity

theorem middle_component_multiplicity
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (family : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (l : V) (hl : l ∈ Paper.HighGirthRounding.middle G x) :
    (Paper.HighGirthComponentCounting.touching G x family l).card ≤ 2 := by
  classical
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    let I := Paper.HighGirthComponentCounting.touching G x family l
    let N := G.neighborFinset l ∩ U
    have hex : ∀ K ∈ I, ∃ u ∈ Paper.HighGirthFreePaths.members G x K, G.Adj l u := by
      intro K hK
      exact (Finset.mem_filter.mp hK).2
    let f : H.ConnectedComponent → V := fun K =>
      if hK : K ∈ I then Classical.choose (hex K hK) else l
    have hf : ∀ K ∈ I, f K ∈ Paper.HighGirthFreePaths.members G x K ∧ G.Adj l (f K) := by
      intro K hK
      simpa only [f,dif_pos hK] using Classical.choose_spec (hex K hK)
    have hmaps : Set.MapsTo f (↑I : Set H.ConnectedComponent) (↑N : Set V) := by
      intro K hK
      obtain ⟨hmem,hadj⟩ := hf K hK
      have huU := (Finset.mem_filter.mp hmem).2.1
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset l (f K)).mpr hadj,huU⟩
    have hinj : Set.InjOn f (↑I : Set H.ConnectedComponent) := by
      intro K hK J hJ heq
      obtain ⟨hKU,hKC⟩ := (Finset.mem_filter.mp (hf K hK).1).2
      obtain ⟨hJU,hJC⟩ := (Finset.mem_filter.mp (hf J hJ).1).2
      have hs : (⟨f K,hKU⟩ : {u // u ∈ U}) = ⟨f J,hJU⟩ := Subtype.ext heq
      exact hKC.symm.trans ((congrArg H.connectedComponentMk hs).trans hJC)
    have hc : I.card ≤ N.card := Finset.card_le_card_of_injOn f hmaps hinj
    by_cases hn : I.Nonempty
    · obtain ⟨K,hK⟩ := hn
      obtain ⟨u,huK,hlu⟩ := hex K hK
      have huU := (Finset.mem_filter.mp huK).2.1
      have hlR := (Finset.mem_sdiff.mp hl).1
      have hd := Paper.HighGirthResidualDegree.residual_neighbor_degree G x l hlR (Or.inr ⟨u,huU,hlu⟩)
      have hsub : N ⊆ G.neighborFinset l ∩ Paper.HighGirthRounding.residual G x := by
        intro z hz
        obtain ⟨hzN,hzU⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨hzN,(Finset.mem_sdiff.mp hzU).1⟩
      exact hc.trans ((Finset.card_le_card hsub).trans hd)
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      change I.card ≤ 2
      simp only [he,Finset.card_empty,Nat.zero_le]

end Paper.HighGirthMiddleMultiplicity

#print axioms Paper.HighGirthMiddleMultiplicity.middle_component_multiplicity
