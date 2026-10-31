import Paper.Endpoints.Girth.HighGirthSpanningCycleEdges
set_option maxHeartbeats 200000
namespace Paper.HighGirthRetainedCycleEdges

theorem retained_nonpath_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hnot : ¬ Paper.HighGirthFreePaths.isPathComponent G x K) :
    Nat.card (G.induce (↑(Paper.HighGirthRetainedSet.parts G x K) : Set V)).edgeSet =
      (Paper.HighGirthRetainedSet.parts G x K).card := by
  classical
    letI : Fintype K := Fintype.ofFinite K
    letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
    let S := Paper.HighGirthRetainedSet.parts G x K
    have hs := Paper.HighGirthRetainedSet.parts_spec G x K
    have hnf : ¬ Paper.HighGirthFreePaths.isFreePath G x K := fun hf => hnot hf.1
    have hS : S = Paper.HighGirthFreePaths.members G x K := hs.2.2.2.2.1 hnf
    have hcycle := Paper.HighGirthResidualComponents.residual_components_path_or_cycle G x K
    rcases hcycle with hp | hc
    · exact (hnot hp).elim
    obtain ⟨a, c, hc, hcover, hgraph⟩ := hc
    have hE := Paper.HighGirthSpanningCycleEdges.spanning_cycle_edges K.toSimpleGraph a c hc hcover hgraph
    let f : K → {v // v ∈ S} := fun z => ⟨z.val.val, by
      rw [hS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨z.val.property, z.property⟩⟩⟩
    have hinj : Function.Injective f := by
      intro u v heq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {v // v ∈ S} => z.val) heq
    have hsur : Function.Surjective f := by
      intro u
      have huK : u.val ∈ Paper.HighGirthFreePaths.members G x K := by
        rw [← hS]
        exact u.property
      obtain ⟨hu, hK⟩ := (Finset.mem_filter.mp huK).2
      refine ⟨⟨⟨u.val, hu⟩, hK⟩, ?_⟩
      rfl
    let e : K.toSimpleGraph ≃g G.induce (↑S : Set V) :=
      { toEquiv := Equiv.ofBijective f ⟨hinj, hsur⟩
        map_rel_iff' := by
          intro u v
          rfl }
    have he := e.card_edgeFinset_eq
    have hv := Fintype.card_congr e.toEquiv
    change Fintype.card K = Fintype.card {v // v ∈ S} at hv
    have hv' : Fintype.card K = S.card := by
      simpa only [Fintype.card_coe] using hv
    change Nat.card (G.induce (↑S : Set V)).edgeSet = S.card
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, ← he, hE, hv']

end Paper.HighGirthRetainedCycleEdges

#print axioms Paper.HighGirthRetainedCycleEdges.retained_nonpath_edge_count
