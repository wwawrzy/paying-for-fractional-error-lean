import Paper.Endpoints.Girth.HighGirthComponentNeighbors
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathNeighborCounts

theorem path_component_neighbor_counts
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : K.toSimpleGraph = p.toSubgraph.spanningCoe) :
    (G.neighborFinset a.val.val ∩ Paper.HighGirthFreePaths.members G x K).card ≤ 1 ∧
    (G.neighborFinset b.val.val ∩ Paper.HighGirthFreePaths.members G x K).card ≤ 1 ∧
    ∀ i : Nat, i ≠ 0 → i < p.length →
      (G.neighborFinset (p.getVert i).val.val ∩ Paper.HighGirthFreePaths.members G x K).card = 2 := by
  classical
    have hns : ∀ z : K, K.toSimpleGraph.neighborSet z = p.toSubgraph.neighborSet z := by
      intro z
      ext w
      exact Iff.of_eq (congrArg (fun F : SimpleGraph K => F.Adj z w) hgraph)
    have hc : ∀ z : K, (G.neighborFinset z.val.val ∩ Paper.HighGirthFreePaths.members G x K).card =
        (p.toSubgraph.neighborSet z).ncard := by
      intro z
      exact (Paper.HighGirthComponentNeighbors.component_neighbor_card G x K z).trans (congrArg Set.ncard (hns z))
    have hbnd : (p.toSubgraph.neighborSet a).ncard ≤ 1 ∧ (p.toSubgraph.neighborSet b).ncard ≤ 1 := by
      by_cases hn : p.Nil
      · cases p with
        | nil => simp [SimpleGraph.Walk.toSubgraph]
        | cons h w => simp at hn
      · constructor
        · rw [hp.neighborSet_toSubgraph_startpoint hn]
          simp
        · rw [hp.neighborSet_toSubgraph_endpoint hn]
          simp
    refine ⟨(hc a).trans_le hbnd.1,(hc b).trans_le hbnd.2,?_⟩
    intro i hi hiL
    exact (hc (p.getVert i)).trans (hp.ncard_neighborSet_toSubgraph_internal_eq_two hi hiL)

end Paper.HighGirthPathNeighborCounts

#print axioms Paper.HighGirthPathNeighborCounts.path_component_neighbor_counts
