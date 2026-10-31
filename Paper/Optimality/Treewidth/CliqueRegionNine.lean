import Paper.Optimality.Treewidth.CliqueRegionBalance
import Paper.Optimality.Treewidth.CliqueExteriorComplementConnected
namespace Paper.CliqueRegionNine
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem bounds (hG : G.IsKMinorFree 7) (S T : Finset V)
    (hdis : Disjoint S T) (hS : S.card = 9) (hT : T.card = 9)
    (hfree : (G.induce (T : Set V)).IsKMinorFree 6)
    (hbase : 28 ≤ G.inducedEdgeCount S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) :
    25 ≤ G.inducedEdgeCount T ∧ G.inducedEdgeCount T ≤ 26 ∧ G.inducedEdgeCount S ≤ 29 := by
  classical
  have card_type (R : Finset V) : Fintype.card (R : Set V) = R.card := by
    simp only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard]
  have hR : (S ∪ T).card = 18 := by rw [Finset.card_union_of_disjoint hdis,hS,hT]
  have heR := SevenCliqueTwentyVertices.edge_bound (G.induce ((S ∪ T : Finset V) : Set V))
    (IsHMinorFree.minor hG (IsMinor.of_induce G _)) (by rw [card_type,hR]; omega) (by rw [card_type,hR]; omega)
  have heT := SixCliqueSharp.edge_bound (G.induce (T : Set V)) hfree (by rw [card_type,hT]; omega)
  rw [card_type,hR] at heR
  rw [card_type,hT] at heT
  change G.inducedEdgeCount (S ∪ T) ≤ 5*18-15 at heR
  change G.inducedEdgeCount T ≤ 4*9-10 at heT
  have hb := CliqueRegionBalance.edge_balance G S T hdis
  have hd : 72 ≤ ∑ x ∈ T, G.inducedDegree x (S ∪ T) := by
    calc
      72 = ∑ _x ∈ T, (8 : ℕ) := by simp [hT]
      _ ≤ _ := Finset.sum_le_sum hdeg
  omega


end Paper.CliqueRegionNine
