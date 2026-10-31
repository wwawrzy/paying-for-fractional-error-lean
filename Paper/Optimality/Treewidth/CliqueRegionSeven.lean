import Paper.Optimality.Treewidth.CliqueRegionCount
import Paper.Optimality.Treewidth.SevenCliqueTwentyVertices
namespace Paper.CliqueRegionSeven
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem seven_le (hG : G.IsKMinorFree 7) (S T : Finset V) (hdis : Disjoint S T)
    (hS : S.card = 9) (hpos : T.Nonempty)
    (hbase : 56 ≤ ∑ x ∈ S, G.inducedDegree x S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) : 7 ≤ T.card := by
  classical
  by_contra hn
  have hsmall : T.card ≤ 6 := by omega
  let R := S ∪ T
  have hR : R.card = 9+T.card := by rw [Finset.card_union_of_disjoint hdis,hS]
  have hcard : Fintype.card (R : Set V) = 9+T.card := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hR
  have hf : (G.induce (R : Set V)).IsKMinorFree 7 := IsHMinorFree.minor hG (IsMinor.of_induce G _)
  have he := SevenCliqueTwentyVertices.edge_bound (G.induce (R : Set V)) hf (by omega) (by omega)
  have hb := CliqueRegionCount.bound G S T hdis T.card rfl hbase hdeg
  change 56+16*T.card ≤ 2*(G.induce (R : Set V)).edgeFinset.card+T.card*(T.card-1) at hb
  have hp : 0 < T.card := Finset.card_pos.mpr hpos
  generalize hk : T.card = k at *
  interval_cases k <;> omega
end Paper.CliqueRegionSeven
