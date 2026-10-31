import Paper.Endpoints.Girth.HighGirthMiddleMultiplicity
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathComponentCount

theorem path_component_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (Paper.HighGirthComponentCounting.nonfreeComponents G x).card ≤
      2 * (Paper.HighGirthRounding.middle G x).card ∧
    (Paper.HighGirthComponentCounting.pathComponents G x).card ≤
      (Paper.HighGirthComponentCounting.freeComponents G x).card +
      2 * (Paper.HighGirthRounding.middle G x).card := by
  classical
  let L := Paper.HighGirthRounding.middle G x
  let P := Paper.HighGirthComponentCounting.pathComponents G x
  let F := Paper.HighGirthComponentCounting.freeComponents G x
  let N := Paper.HighGirthComponentCounting.nonfreeComponents G x
  have hex : ∀ K ∈ N, ∃ l ∈ L, K ∈ Paper.HighGirthComponentCounting.touching G x P l := by
    intro K hK
    obtain ⟨hKP, hKF⟩ := Finset.mem_sdiff.mp hK
    have hnotfree : ¬ Paper.HighGirthFreePaths.free G x K := by
      intro hf
      exact hKF (Finset.mem_filter.mpr ⟨hKP, hf⟩)
    change ¬ (∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      ∀ l ∈ Paper.HighGirthRounding.middle G x, ¬ G.Adj u l) at hnotfree
    push Not at hnotfree
    obtain ⟨u, hu, l, hl, hadj⟩ := hnotfree
    exact ⟨l, hl, Finset.mem_filter.mpr ⟨hKP, ⟨u, hu, hadj.symm⟩⟩⟩
  have hsub : N ⊆ L.biUnion (Paper.HighGirthComponentCounting.touching G x P) := by
    intro K hK
    obtain ⟨l, hl, hKl⟩ := hex K hK
    exact Finset.mem_biUnion.mpr ⟨l, hl, hKl⟩
  have hbi := Finset.card_biUnion_le_card_mul L (Paper.HighGirthComponentCounting.touching G x P) 2
    (fun l hl => Paper.HighGirthMiddleMultiplicity.middle_component_multiplicity G x P l hl)
  have hN : N.card ≤ 2 * L.card := by
    have h := (Finset.card_le_card hsub).trans hbi
    simpa only [Nat.mul_comm] using h
  have hFP : F ⊆ P := Finset.filter_subset _ _
  have hsplit : N.card + F.card = P.card := Finset.card_sdiff_add_card_eq_card hFP
  constructor
  · exact hN
  · change P.card ≤ F.card + 2 * L.card
    omega

end Paper.HighGirthPathComponentCount

#print axioms Paper.HighGirthPathComponentCount.path_component_count
