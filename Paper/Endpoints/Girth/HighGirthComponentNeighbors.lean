import Paper.Endpoints.Girth.HighGirthFreeEndpoints
set_option maxHeartbeats 200000
namespace Paper.HighGirthComponentNeighbors

theorem component_neighbor_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (z : K) :
    (G.neighborFinset z.val.val ∩ Paper.HighGirthFreePaths.members G x K).card =
      (K.toSimpleGraph.neighborSet z).ncard := by
  classical
    letI : Fintype K := Fintype.ofFinite K
    let e : K ↪ V := ⟨fun a => a.val.val, by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact hab⟩
    have hmap : (K.toSimpleGraph.neighborFinset z).map e =
        G.neighborFinset z.val.val ∩ Paper.HighGirthFreePaths.members G x K := by
      ext v
      constructor
      · intro hv
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
        have hadj : G.Adj z.val.val a.val.val := (K.toSimpleGraph.mem_neighborFinset z a).mp ha
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩⟩
      · intro hv
        obtain ⟨hvn,hvK⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvU,hvComp⟩ := (Finset.mem_filter.mp hvK).2
        let a : K := ⟨⟨v,hvU⟩,hvComp⟩
        have hadj : K.toSimpleGraph.Adj z a := (G.mem_neighborFinset _ _).mp hvn
        exact Finset.mem_map.mpr ⟨a,(K.toSimpleGraph.mem_neighborFinset z a).mpr hadj,rfl⟩
    rw [Set.ncard_eq_toFinset_card']
    change (G.neighborFinset z.val.val ∩ Paper.HighGirthFreePaths.members G x K).card =
      (K.toSimpleGraph.neighborFinset z).card
    simpa only [Finset.card_map] using (congrArg Finset.card hmap).symm

end Paper.HighGirthComponentNeighbors

#print axioms Paper.HighGirthComponentNeighbors.component_neighbor_card
