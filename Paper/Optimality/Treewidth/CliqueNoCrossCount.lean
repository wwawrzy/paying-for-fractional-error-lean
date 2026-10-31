import Paper.Optimality.Treewidth.CliqueRegionBalance
namespace Paper.CliqueNoCrossCount
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem edges_union (X Y : Finset V) (hdis : Disjoint X Y)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬G.Adj x y) :
    G.inducedEdgeCount (X ∪ Y) = G.inducedEdgeCount X+G.inducedEdgeCount Y := by
  classical
  have hz : ∀ y ∈ Y, G.inducedDegree y X = 0 := by
    intro y hy
    change (X.filter (G.Adj y)).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx,h⟩ := Finset.mem_filter.mp hx
    exact hno x hx y hy h.symm
  have hsum : (∑ y ∈ Y, G.inducedDegree y (X ∪ Y)) = 2*G.inducedEdgeCount Y := by
    simp_rw [CliqueRegionCount.degree_union G X Y hdis]
    rw [Finset.sum_add_distrib,Finset.sum_eq_zero hz,zero_add]
    exact InducedCounting.sum_inducedDegree_eq_two_mul G Y
  have hh := CliqueRegionBalance.edge_balance G X Y hdis
  omega

theorem degree_univ (x : V) : G.inducedDegree x Finset.univ = G.degree x := by
  classical
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by ext y; simp
  change (Finset.univ.filter (G.Adj x)).card = G.degree x
  rw [he,G.card_neighborFinset_eq_degree]

theorem edges_univ : G.inducedEdgeCount Finset.univ = G.edgeFinset.card := by
  have hh := InducedCounting.sum_inducedDegree_eq_two_mul G Finset.univ
  simp_rw [degree_univ G] at hh
  have hs := G.sum_degrees_eq_twice_card_edges
  omega

end Paper.CliqueNoCrossCount
