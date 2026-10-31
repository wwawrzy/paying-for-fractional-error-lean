import Paper.Endpoints.Girth.HighGirthRetainedEdgeSum

namespace Paper.HighGirthRetainedEdgeCount

theorem retained_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    Nat.card (G.induce (↑(HighGirthRetainedSet.vertices G x) : Set V)).edgeSet +
      (HighGirthComponentCounting.pathComponents G x).card =
      (HighGirthRetainedSet.vertices G x).card := by
  classical
  have hpoint : ∀ K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent,
      Nat.card (G.induce (↑(HighGirthRetainedSet.parts G x K) : Set V)).edgeSet +
        (if HighGirthFreePaths.isPathComponent G x K then 1 else 0) =
        (HighGirthRetainedSet.parts G x K).card := by
    intro K
    by_cases hp : HighGirthFreePaths.isPathComponent G x K
    · simpa only [hp,ite_true] using (HighGirthRetainedPathEdges.retained_path_is_tree_and_edge_count G x K hp).2
    · simpa only [hp,ite_false,Nat.add_zero] using HighGirthRetainedCycleEdges.retained_nonpath_edge_count G x K hp
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun K _ => hpoint K)
  have hcp : (∑ K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent,
      if HighGirthFreePaths.isPathComponent G x K then 1 else 0) =
      (HighGirthComponentCounting.pathComponents G x).card := by
    simp [HighGirthComponentCounting.pathComponents]
  rw [Finset.sum_add_distrib,hcp,←HighGirthRetainedEdgeSum.retained_edge_card_sum G x,
    ←(HighGirthRetainedPartition.retained_set_partition G x).2.2.2] at hsum
  exact hsum

end Paper.HighGirthRetainedEdgeCount
#print axioms Paper.HighGirthRetainedEdgeCount.retained_edge_count
