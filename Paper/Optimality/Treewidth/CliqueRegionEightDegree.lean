import Paper.Optimality.Treewidth.CliqueRegionEight
namespace Paper.CliqueRegionEightDegree
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem regular (hG : G.IsKMinorFree 7) (S T : Finset V)
    (hdis : Disjoint S T) (hS : S.card = 9) (hT : T.card = 8)
    (hfree : (G.induce (T : Set V)).IsKMinorFree 6)
    (hbase : 28 ≤ G.inducedEdgeCount S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) :
    ∀ x ∈ T, G.inducedDegree x (S ∪ T) = 8 := by
  classical
  obtain ⟨heT,heS⟩ := CliqueRegionEight.exact_counts G hG S T hdis hS hT hfree hbase hdeg
  have card_type (R : Finset V) : Fintype.card (R : Set V) = R.card := by
    simp only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard]
  have hR : (S ∪ T).card = 17 := by rw [Finset.card_union_of_disjoint hdis,hS,hT]
  have heR := SevenCliqueTwentyVertices.edge_bound (G.induce ((S ∪ T : Finset V) : Set V))
    (IsHMinorFree.minor hG (IsMinor.of_induce G _)) (by rw [card_type,hR]; omega) (by rw [card_type,hR]; omega)
  rw [card_type,hR] at heR
  change G.inducedEdgeCount (S ∪ T) ≤ 5*17-15 at heR
  have hb := CliqueRegionBalance.edge_balance G S T hdis
  intro x hx
  have hrest : 56 ≤ ∑ y ∈ T.erase x, G.inducedDegree y (S ∪ T) := by
    calc
      56 = ∑ _y ∈ T.erase x, (8 : ℕ) := by simp [Finset.card_erase_of_mem hx,hT]
      _ ≤ _ := Finset.sum_le_sum (fun y hy => hdeg y (Finset.mem_erase.mp hy).2)
  have hs := Finset.sum_erase_add T (fun y => G.inducedDegree y (S ∪ T)) hx
  change (∑ y ∈ T.erase x, G.inducedDegree y (S ∪ T))+G.inducedDegree x (S ∪ T) =
    ∑ y ∈ T, G.inducedDegree y (S ∪ T) at hs
  have hd := hdeg x hx
  omega
end Paper.CliqueRegionEightDegree
