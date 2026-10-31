import Paper.Endpoints.Girth.HighGirthInducedEdgeSets
set_option maxHeartbeats 200000
namespace Paper.HighGirthRetainedEdgeSum
theorem retained_edge_card_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    Nat.card (G.induce (↑(Paper.HighGirthRetainedSet.vertices G x) : Set V)).edgeSet =
      ∑ K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent,
        Nat.card (G.induce (↑(Paper.HighGirthRetainedSet.parts G x K) : Set V)).edgeSet := by
  classical
  let S := Paper.HighGirthRetainedSet.vertices G x
  let R := Paper.HighGirthRetainedSet.parts G x
  let E := Paper.HighGirthInducedEdgeSets.edges G
  have hs := Paper.HighGirthRetainedSet.parts_spec G x
  have hp := Paper.HighGirthRetainedPartition.retained_set_partition G x
  have hmem : ∀ (T : Finset V) (u v : V), s(u,v) ∈ E T ↔ G.Adj u v ∧ u ∈ T ∧ v ∈ T := by
    intro T u v
    simp [E,Paper.HighGirthInducedEdgeSets.edges,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,Finset.mk_mem_sym2_iff]
  have hsub : ∀ K, R K ⊆ S := by
    intro K u hu
    exact Finset.mem_biUnion.mpr ⟨K,Finset.mem_univ _,hu⟩
  have huniq : ∀ K J (u : V), u ∈ Paper.HighGirthFreePaths.members G x K →
      u ∈ Paper.HighGirthFreePaths.members G x J → K = J := by
    intro K J u huK huJ
    obtain ⟨hu,hK⟩ := (Finset.mem_filter.mp huK).2
    obtain ⟨hu',hJ⟩ := (Finset.mem_filter.mp huJ).2
    exact hK.symm.trans hJ
  have hdis : (↑(Finset.univ : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
      Set (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent).PairwiseDisjoint (fun K => E (R K)) := by
    intro K _ J _ hne
    apply Finset.disjoint_left.mpr
    intro e heK heJ
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huK := ((hmem (R K) u v).mp heK).2.1
      have huJ := ((hmem (R J) u v).mp heJ).2.1
      exact hne (huniq K J u ((hs K).2.1 huK) ((hs J).2.1 huJ))
  have hcover : E S = Finset.univ.biUnion (fun K => E (R K)) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      constructor
      · intro he
        obtain ⟨hadj,huS,hvS⟩ := (hmem S u v).mp he
        have huU : u ∈ Paper.HighGirthRounding.last G x := hp.1 huS
        have hvU : v ∈ Paper.HighGirthRounding.last G x := hp.1 hvS
        let K := (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).connectedComponentMk ⟨u,huU⟩
        have huK : u ∈ Paper.HighGirthFreePaths.members G x K :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨huU,rfl⟩⟩
        have hvK := Paper.HighGirthComponentBalls.adjacent_member G x K u v huK hvU hadj
        have huR : u ∈ R K := by
          change u ∈ Paper.HighGirthRetainedSet.parts G x K
          rw [←hp.2.2.1 K]
          exact Finset.mem_inter.mpr ⟨huS,huK⟩
        have hvR : v ∈ R K := by
          change v ∈ Paper.HighGirthRetainedSet.parts G x K
          rw [←hp.2.2.1 K]
          exact Finset.mem_inter.mpr ⟨hvS,hvK⟩
        exact Finset.mem_biUnion.mpr ⟨K,Finset.mem_univ _,(hmem (R K) u v).mpr ⟨hadj,huR,hvR⟩⟩
      · intro he
        obtain ⟨K,_,heK⟩ := Finset.mem_biUnion.mp he
        obtain ⟨hadj,huR,hvR⟩ := (hmem (R K) u v).mp heK
        exact (hmem S u v).mpr ⟨hadj,hsub K huR,hsub K hvR⟩
  calc
    _ = (E S).card := (Paper.HighGirthInducedEdgeSets.edges_card G S).symm
    _ = (Finset.univ.biUnion (fun K => E (R K))).card := congrArg Finset.card hcover
    _ = ∑ K, (E (R K)).card := Finset.card_biUnion hdis
    _ = _ := by
      apply Finset.sum_congr rfl
      intro K hK
      exact Paper.HighGirthInducedEdgeSets.edges_card G (R K)
end Paper.HighGirthRetainedEdgeSum
#print axioms Paper.HighGirthRetainedEdgeSum.retained_edge_card_sum
