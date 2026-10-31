import Paper.Endpoints.Girth.HighGirthFreeClassBounds
import Mathlib.Combinatorics.SimpleGraph.Acyclic
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathTree

theorem path_component_is_tree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hpath : Paper.HighGirthFreePaths.isPathComponent G x K) :
    K.toSimpleGraph.IsTree := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hpath
  have heSet : K.toSimpleGraph.edgeSet = p.toSubgraph.edgeSet :=
    (congrArg SimpleGraph.edgeSet hgraph).trans p.toSubgraph.edgeSet_spanningCoe
  have he : K.toSimpleGraph.edgeFinset = p.edges.toFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,List.mem_toFinset,heSet]
    exact p.mem_edges_toSubgraph
  have hEcard : K.toSimpleGraph.edgeFinset.card = p.length := by
    rw [he,List.toFinset_card_of_nodup hp.isTrail.edges_nodup,SimpleGraph.Walk.length_edges]
  have hs : p.support.toFinset = Finset.univ := by
    ext z
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hcover z
  have hVcard : Fintype.card K = p.length + 1 := by
    have hh := congrArg Finset.card hs
    simpa only [List.toFinset_card_of_nodup hp.support_nodup,SimpleGraph.Walk.length_support,Finset.card_univ] using hh.symm
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨K.connected_toSimpleGraph,?_⟩
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet,hEcard,Nat.card_eq_fintype_card]
  exact hVcard.symm

end Paper.HighGirthPathTree

#print axioms Paper.HighGirthPathTree.path_component_is_tree
