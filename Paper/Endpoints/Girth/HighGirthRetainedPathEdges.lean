import Paper.Endpoints.Girth.HighGirthRetainedSize
set_option maxHeartbeats 200000
namespace Paper.HighGirthRetainedPathEdges
theorem retained_path_is_tree_and_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hpath : Paper.HighGirthFreePaths.isPathComponent G x K) :
    (G.induce (↑(Paper.HighGirthRetainedSet.parts G x K) : Set V)).IsTree ∧
    Nat.card (G.induce (↑(Paper.HighGirthRetainedSet.parts G x K) : Set V)).edgeSet + 1 =
      (Paper.HighGirthRetainedSet.parts G x K).card := by
  classical
  let S := Paper.HighGirthRetainedSet.parts G x K
  have hs := Paper.HighGirthRetainedSet.parts_spec G x K
  have hu : ∀ u : {v // v ∈ S}, ∃ hv : u.val ∈ Paper.HighGirthRounding.last G x,
      (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).connectedComponentMk ⟨u.val,hv⟩ = K := by
    intro u
    exact (Finset.mem_filter.mp (hs.2.1 u.property)).2
  let f : G.induce (↑S : Set V) →g K.toSimpleGraph :=
    ⟨fun u => ⟨⟨u.val,Classical.choose (hu u)⟩,Classical.choose_spec (hu u)⟩,
      by intro u v huv; exact huv⟩
  have hinj : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun w : K => w.val.val) he
  have hacyc : (G.induce (↑S : Set V)).IsAcyclic :=
    SimpleGraph.IsAcyclic.comap f hinj (Paper.HighGirthPathTree.path_component_is_tree G x K hpath).isAcyclic
  have hc : (G.induce (↑S : Set V)).Connected := hs.2.2.1
  have ht : (G.induce (↑S : Set V)).IsTree := { connected := hc, isAcyclic := hacyc }
  constructor
  · exact ht
  · have he := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
    have hv : Nat.card {v // v ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    change Nat.card (G.induce (↑S : Set V)).edgeSet + 1 = Nat.card {v // v ∈ S} at he
    rw [hv] at he
    exact he
end Paper.HighGirthRetainedPathEdges
#print axioms Paper.HighGirthRetainedPathEdges.retained_path_is_tree_and_edge_count
