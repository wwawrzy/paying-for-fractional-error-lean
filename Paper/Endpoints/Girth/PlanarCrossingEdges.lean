import Paper.Endpoints.Girth.CurrentPlanarFaceBound
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-! # Actual planar bipartite crossing graphs -/

namespace Paper.PlanarCrossingEdges

open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem girth_four_of_bipartite (hb : G.IsBipartite)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 4 ≤ c.length := by
  have hthree := hc.three_le_length
  obtain ⟨k, hk⟩ := (two_colorable_iff_forall_loop_even.mp hb) v c
  omega

theorem between_degree (X Y : Finset V) (hXY : Disjoint X Y)
    (a : V) (ha : a ∈ X) :
    (G.between (X : Set V) (Y : Set V)).degree a =
      (Y.filter (G.Adj a)).card := by
  have haY : a ∉ Y := fun h => Finset.disjoint_left.mp hXY ha h
  have heq : (G.between (X : Set V) (Y : Set V)).neighborFinset a =
      Y.filter (G.Adj a) := by
    ext b
    simp only [mem_neighborFinset, between_adj, Finset.mem_coe,
      Finset.mem_filter, ha, haY, true_and, false_and, or_false]
    exact and_comm
  rw [← card_neighborFinset_eq_degree, heq]

theorem between_edge_card_eq_interedges (X Y : Finset V) (hXY : Disjoint X Y) :
    (G.between (X : Set V) (Y : Set V)).edgeFinset.card =
      (G.interedges X Y).card := by
  have hb := between_isBipartiteWith (G := G) (Finset.disjoint_coe.mpr hXY)
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (s := X) (t := Y) hb,
    Incidence.card_interedges_eq_sum]
  exact Finset.sum_congr rfl (fun a ha => between_degree G X Y hXY a ha)

/-- The count uses the actual crossing subgraph and only the vertices in
the two parts. Isolated ambient vertices do not enlarge the bound. -/
theorem planar_interedges_bound (hplanar : G.IsPlanar)
    (X Y : Finset V) (hXY : Disjoint X Y) :
    (G.interedges X Y).card ≤ 2 * (X.card + Y.card) := by
  let H := G.between (X : Set V) (Y : Set V)
  have hb : H.IsBipartite := between_isBipartite (G := G) (Finset.disjoint_coe.mpr hXY)
  have hp : H.IsPlanar := hplanar.mono (between_le (G := G))
  have hsupp : H.support ⊆ ((X ∪ Y : Finset V) : Set V) := by
    simpa only [Finset.coe_union] using
      (isBipartiteWith_support_subset
        (between_isBipartiteWith (G := G) (Finset.disjoint_coe.mpr hXY)))
  have hs : H.inducedEdgeCount (X ∪ Y) = H.edgeFinset.card := by
    simpa only [SimpleGraph.inducedEdgeCount, edgeFinset_card,
      ← Nat.card_eq_fintype_card] using
      (card_edgeFinset_induce_of_support_subset
        (G := H) (s := ((X ∪ Y : Finset V) : Set V)) hsupp)
  have hd := CurrentPlanarFaceBound.induced_density hp 4 (by omega)
    (girth_four_of_bipartite H hb) (X ∪ Y)
  norm_num at hd
  rw [hs] at hd
  have hnat : H.edgeFinset.card ≤ 2 * (X ∪ Y).card := by exact_mod_cast hd
  rw [← between_edge_card_eq_interedges G X Y hXY]
  exact hnat.trans (Nat.mul_le_mul_left 2 (Finset.card_union_le X Y))

end Paper.PlanarCrossingEdges

#print axioms Paper.PlanarCrossingEdges.girth_four_of_bipartite
#print axioms Paper.PlanarCrossingEdges.between_degree
#print axioms Paper.PlanarCrossingEdges.between_edge_card_eq_interedges
#print axioms Paper.PlanarCrossingEdges.planar_interedges_bound
