import Paper.Optimality.Treewidth.SevenCliqueProjection
import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.SevenCliqueNineSmallOrder
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem order_thirteen (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 9)
    (hmin : ∀ z, G.degree v ≤ G.degree z) : 13 ≤ Fintype.card V := by
  classical
  by_contra hn
  have horder : Fintype.card V ≤ 12 := by omega
  let N := G.neighborFinset v
  let H := G.induce (N : Set V)
  have hN : N.card = 9 := by exact (G.card_neighborFinset_eq_degree v).trans hv
  have hcard : Fintype.card (N : Set V) = 9 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hN
  have hdeg : ∀ w : (N : Set V), 6 ≤ H.degree w := by
    intro w
    have hp := CliquePartitionDegrees.partition G N w.val
    have hc : G.inducedDegree w.val Nᶜ ≤ 3 := by
      have hh := Finset.card_filter_le Nᶜ (G.Adj w.val)
      rw [Finset.card_compl,hN] at hh
      change G.inducedDegree w.val Nᶜ ≤ _ at hh
      omega
    have hl := hmin w.val
    have he := InducedCounting.degree_induce_eq_inducedDegree G N w
    change H.degree w = G.inducedDegree w.val N at he
    rw [hv] at hl
    omega
  have hu : v ∉ (N : Set V) := G.notMem_neighborFinset_self v
  have hb := SevenCliqueProjection.edge_bound G H hG
    (SevenCliqueProjection.induced_model G (N : Set V)) v
    (by intro w hw; exact hu (hw ▸ w.property))
    (by intro w; exact ⟨w.val,rfl,(G.mem_neighborFinset v w.val).mp w.property⟩)
    (by omega)
  letI : Nonempty (N : Set V) := Fintype.card_pos_iff.mp (by omega)
  have hm : 6 ≤ H.minDegree := H.le_minDegree_of_forall_le_degree 6 hdeg
  have hs := H.minDegree_mul_card_le_two_mul_card_edges
  have hmul := Nat.mul_le_mul_right (Fintype.card (N : Set V)) hm
  rw [hcard] at hb hs hmul
  omega
end Paper.SevenCliqueNineSmallOrder
