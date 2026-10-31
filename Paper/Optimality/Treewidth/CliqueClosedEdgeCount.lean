import Paper.Optimality.Treewidth.CliqueRegionBalance
namespace Paper.CliqueClosedEdgeCount
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem identity (v : V) :
    G.inducedEdgeCount (insert v (G.neighborFinset v)) =
      G.inducedEdgeCount (G.neighborFinset v)+G.degree v := by
  classical
  let N := G.neighborFinset v
  have hdis : Disjoint N ({v} : Finset V) := by simp [N,G.notMem_neighborFinset_self v]
  have hb := CliqueRegionBalance.edge_balance G N {v} hdis
  have he : N ∪ {v} = insert v N := by ext x; simp [or_comm]
  have hz : G.inducedEdgeCount {v} = 0 := by
    have hh := InducedCounting.sum_inducedDegree_eq_two_mul G {v}
    have hd : G.inducedDegree v {v} = 0 := by simp [SimpleGraph.inducedDegree]
    simp only [Finset.sum_singleton,hd] at hh
    omega
  have hd : G.inducedDegree v (N ∪ {v}) = G.degree v := by
    have hf : (N ∪ {v}).filter (G.Adj v) = N := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_singleton,N,G.mem_neighborFinset]
      tauto
    change ((N ∪ {v}).filter (G.Adj v)).card = G.degree v
    rw [hf,G.card_neighborFinset_eq_degree]
  rw [Finset.sum_singleton,hd,hz,he] at hb
  omega
end Paper.CliqueClosedEdgeCount
