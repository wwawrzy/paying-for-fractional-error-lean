import Paper.Endpoints.Girth.HighGirthRetainedPathEdges

namespace Paper.HighGirthSpanningCycleEdges

theorem spanning_cycle_edges
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (a : W) (c : H.Walk a a) (hc : c.IsCycle)
    (hcover : ∀ z : W, z ∈ c.support)
    (hgraph : H = c.toSubgraph.spanningCoe) :
    H.edgeFinset.card = Fintype.card W := by
  classical
  have heSet : H.edgeSet = c.toSubgraph.edgeSet :=
    (congrArg SimpleGraph.edgeSet hgraph).trans c.toSubgraph.edgeSet_spanningCoe
  have he : H.edgeFinset = c.edges.toFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,List.mem_toFinset,heSet]
    exact c.mem_edges_toSubgraph
  have hEcard : H.edgeFinset.card = c.length := by
    rw [he,List.toFinset_card_of_nodup hc.isTrail.edges_nodup,SimpleGraph.Walk.length_edges]
  have htail : c.support.tail.toFinset = Finset.univ := by
    ext z
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    have hz := hcover z
    rw [c.support_eq_cons,List.mem_cons] at hz
    rcases hz with heq | hz
    · subst z
      exact c.end_mem_tail_support hc.not_nil
    · exact hz
  have hv : Fintype.card W = c.length := by
    have hh := congrArg Finset.card htail
    simpa only [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,
      SimpleGraph.Walk.length_support,Nat.add_sub_cancel,Finset.card_univ] using hh.symm
  exact hEcard.trans hv.symm

end Paper.HighGirthSpanningCycleEdges
#print axioms Paper.HighGirthSpanningCycleEdges.spanning_cycle_edges
