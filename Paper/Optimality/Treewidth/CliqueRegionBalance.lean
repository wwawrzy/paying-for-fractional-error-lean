import Paper.Optimality.Treewidth.CliqueRegionCount
import Paper.Optimality.Treewidth.SevenCliqueTwentyVertices
namespace Paper.CliqueRegionBalance
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem edge_balance (S T : Finset V) (hdis : Disjoint S T) :
    G.inducedEdgeCount (S ∪ T)+G.inducedEdgeCount T =
      G.inducedEdgeCount S+∑ x ∈ T, G.inducedDegree x (S ∪ T) := by
  classical
  have hc := CliquePartitionDegrees.cross_sum G S T
  have hs := InducedCounting.sum_inducedDegree_eq_two_mul G S
  have ht := InducedCounting.sum_inducedDegree_eq_two_mul G T
  have hr := InducedCounting.sum_inducedDegree_eq_two_mul G (S ∪ T)
  rw [Finset.sum_union hdis] at hr
  have h1 : (∑ x ∈ S, G.inducedDegree x (S ∪ T)) =
      (∑ x ∈ S, G.inducedDegree x S)+(∑ x ∈ S, G.inducedDegree x T) := by
    simp_rw [CliqueRegionCount.degree_union G S T hdis]
    exact Finset.sum_add_distrib
  have h2 : (∑ x ∈ T, G.inducedDegree x (S ∪ T)) =
      (∑ x ∈ T, G.inducedDegree x S)+(∑ x ∈ T, G.inducedDegree x T) := by
    simp_rw [CliqueRegionCount.degree_union G S T hdis]
    exact Finset.sum_add_distrib
  omega

theorem seven_internal (hG : G.IsKMinorFree 7) (S T : Finset V)
    (hdis : Disjoint S T) (hS : S.card = 9) (hT : T.card = 7)
    (hbase : 28 ≤ G.inducedEdgeCount S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) :
    19 ≤ G.inducedEdgeCount T ∧ G.inducedEdgeCount T ≤ 20 ∧
    G.inducedEdgeCount S ≤ 29 := by
  classical
  have card_type (R : Finset V) : Fintype.card (R : Set V) = R.card := by
    simp only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard]
  have hR : (S ∪ T).card = 16 := by rw [Finset.card_union_of_disjoint hdis,hS,hT]
  have heR := SevenCliqueTwentyVertices.edge_bound (G.induce ((S ∪ T : Finset V) : Set V))
    (IsHMinorFree.minor hG (IsMinor.of_induce G _)) (by rw [card_type,hR]; omega) (by rw [card_type,hR]; omega)
  have heT := SevenCliqueTwentyVertices.edge_bound (G.induce (T : Set V))
    (IsHMinorFree.minor hG (IsMinor.of_induce G _)) (by rw [card_type,hT]; omega) (by rw [card_type,hT]; omega)
  rw [card_type,hR] at heR
  rw [card_type,hT] at heT
  change G.inducedEdgeCount (S ∪ T) ≤ 5*16-15 at heR
  change G.inducedEdgeCount T ≤ 5*7-15 at heT
  have hb := edge_balance G S T hdis
  have hd : 56 ≤ ∑ x ∈ T, G.inducedDegree x (S ∪ T) := by
    calc
      56 = ∑ _x ∈ T, (8 : ℕ) := by simp [hT]
      _ ≤ _ := Finset.sum_le_sum hdeg
  omega

/-- The only remaining seven-vertex side already contains a genuine K6 model. -/
theorem seven_six_model (hG : G.IsKMinorFree 7) (S T : Finset V)
    (hdis : Disjoint S T) (hS : S.card = 9) (hT : T.card = 7)
    (hbase : 28 ≤ G.inducedEdgeCount S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) :
    Nonempty (MinorModel (completeGraph (Fin 6)) (G.induce (T : Set V))) := by
  classical
  have hnineteen := (seven_internal G hG S T hdis hS hT hbase hdeg).1
  by_contra hn
  have hfree : (G.induce (T : Set V)).IsKMinorFree 6 := by
    intro hm
    exact hn hm
  have hcard : Fintype.card (T : Set V) = 7 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hT
  have he := SixCliqueSharp.edge_bound (G.induce (T : Set V)) hfree (by omega)
  rw [hcard] at he
  change 19 ≤ (G.induce (T : Set V)).edgeFinset.card at hnineteen
  omega

end Paper.CliqueRegionBalance

