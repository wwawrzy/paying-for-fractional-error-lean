import Paper.Optimality.Treewidth.SevenCliqueFourteenVertices
import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.CliqueRegionCount
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem degree_union (S T : Finset V) (hdis : Disjoint S T) (x : V) :
    G.inducedDegree x (S ∪ T) = G.inducedDegree x S+G.inducedDegree x T := by
  classical
  unfold SimpleGraph.inducedDegree
  rw [Finset.filter_union,Finset.card_union_of_disjoint
    (hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

theorem bound (S T : Finset V) (hdis : Disjoint S T) (k : ℕ) (hk : T.card = k)
    (hbase : 56 ≤ ∑ x ∈ S, G.inducedDegree x S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) :
    56+16*k ≤ 2*G.inducedEdgeCount (S ∪ T)+k*(k-1) := by
  classical
  have hinside : ∀ x ∈ T, G.inducedDegree x T ≤ k-1 := by
    intro x hx
    have hs : T.filter (G.Adj x) ⊆ T.erase x := by
      intro y hy
      obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_erase.mpr ⟨hxy.ne.symm,hyT⟩
    have hh := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hx,hk] at hh
    exact hh
  have hsmall : (∑ x ∈ T, G.inducedDegree x T) ≤ k*(k-1) := by
    calc
      _ ≤ ∑ _x ∈ T, (k-1) := Finset.sum_le_sum hinside
      _ = _ := by simp [hk]
  have hlarge : 8*k ≤ ∑ x ∈ T, G.inducedDegree x (S ∪ T) := by
    calc
      _ = ∑ _x ∈ T, (8 : ℕ) := by simp [hk,Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hdeg
  have hcross := CliquePartitionDegrees.cross_sum G S T
  have hSdeg : (∑ x ∈ S, G.inducedDegree x (S ∪ T)) =
      (∑ x ∈ S, G.inducedDegree x S)+(∑ x ∈ S, G.inducedDegree x T) := by
    simp_rw [degree_union G S T hdis]
    exact Finset.sum_add_distrib
  have hTdeg : (∑ x ∈ T, G.inducedDegree x (S ∪ T)) =
      (∑ x ∈ T, G.inducedDegree x S)+(∑ x ∈ T, G.inducedDegree x T) := by
    simp_rw [degree_union G S T hdis]
    exact Finset.sum_add_distrib
  have hsplit : (∑ x ∈ S, G.inducedDegree x (S ∪ T))+
      (∑ x ∈ T, G.inducedDegree x (S ∪ T)) = 2*G.inducedEdgeCount (S ∪ T) := by
    rw [← Finset.sum_union hdis]
    exact InducedCounting.sum_inducedDegree_eq_two_mul G (S ∪ T)
  omega

theorem six_le (hG : G.IsKMinorFree 7) (S T : Finset V) (hdis : Disjoint S T)
    (hS : S.card = 9) (hpos : T.Nonempty)
    (hbase : 56 ≤ ∑ x ∈ S, G.inducedDegree x S)
    (hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T)) : 6 ≤ T.card := by
  classical
  by_contra hn
  have hsmall : T.card ≤ 5 := by omega
  let R := S ∪ T
  have hR : R.card = 9+T.card := by rw [Finset.card_union_of_disjoint hdis,hS]
  have hcard : Fintype.card (R : Set V) = 9+T.card := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hR
  have hf : (G.induce (R : Set V)).IsKMinorFree 7 := IsHMinorFree.minor hG (IsMinor.of_induce G _)
  have he := SevenCliqueFourteenVertices.edge_bound (G.induce (R : Set V)) hf (by omega) (by omega)
  have hb := bound G S T hdis T.card rfl hbase hdeg
  change 56+16*T.card ≤ 2*(G.induce (R : Set V)).edgeFinset.card+T.card*(T.card-1) at hb
  have hp : 0 < T.card := Finset.card_pos.mpr hpos
  generalize hk : T.card = k at *
  interval_cases k <;> omega
end Paper.CliqueRegionCount
