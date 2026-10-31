import Paper.Preliminaries.Incidence

/-! Weighted open-incidence bounds from the density of actual induced
subgraphs. The positive part of the incidence-degree excess replaces a
fractional orientation, so no orientation or desired weighted bound is an
assumption. This is the counting input for neighborhood slack. -/

namespace Paper.Density.NeighborhoodSlack

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def hits (S : Finset V) (v : V) : ℕ := (G.neighborFinset v ∩ S).card

theorem card_interedges (T S : Finset V) :
    (G.interedges T S).card = ∑ v ∈ T, hits G S v := by
  rw [Incidence.card_interedges_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  exact and_comm

theorem incidence_sum (S T : Finset V) (z : V → ℝ) :
    (∑ s ∈ S, ∑ v ∈ G.neighborFinset s ∩ T, z v) =
      ∑ v ∈ T, (hits G S v : ℝ) * z v := by
  classical
  calc
    _ = ∑ s ∈ S, ∑ v ∈ T, if G.Adj s v then z v else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    _ = ∑ v ∈ T, ∑ s ∈ S, if G.Adj s v then z v else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [G.adj_comm _ v]
      rw [← Finset.sum_filter]
      have he : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
      rw [he]
      simp [hits]

theorem unweighted_incidence_le (a : ℝ) (hden : Incidence.InducedDensityBound G a)
    (T S : Finset V) :
    (∑ v ∈ T, (hits G S v : ℝ)) ≤ a * T.card + a * S.card := by
  have hn := Incidence.card_interedges_le G T S
  rw [card_interedges G T S] at hn
  have hr : (∑ v ∈ T, (hits G S v : ℝ)) ≤
      (G.inducedEdgeCount (T ∪ S) : ℝ) + (G.inducedEdgeCount (T ∩ S) : ℝ) :=
    by exact_mod_cast hn
  have hc : ((T ∪ S).card : ℝ) + (T ∩ S).card = (T.card : ℝ) + S.card :=
    by exact_mod_cast Finset.card_union_add_card_inter T S
  have hw := congrArg (fun q : ℝ => a * q) hc
  nlinarith only [hr, hden (T ∪ S), hden (T ∩ S), hw]

/-- The full weighted incidence inequality follows directly from density,
including when S and T overlap. Only the weights on T are constrained. -/
theorem weighted_incidence_le (a : ℝ) (hden : Incidence.InducedDensityBound G a)
    (S T : Finset V) (z : V → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hz : ∀ v ∈ T, 0 ≤ z v) (hcap : ∀ v ∈ T, z v ≤ t) :
    (∑ s ∈ S, ∑ v ∈ G.neighborFinset s ∩ T, z v) ≤
      a * (∑ v ∈ T, z v) + a * t * S.card := by
  classical
  let U := T.filter (fun v => a < (hits G S v : ℝ))
  have hexcess : (∑ v ∈ U, ((hits G S v : ℝ) - a)) ≤ a * S.card := by
    have hb := unweighted_incidence_le G a hden U S
    have he : (∑ v ∈ U, ((hits G S v : ℝ) - a)) =
        (∑ v ∈ U, (hits G S v : ℝ)) - a * U.card := by
      simp [Finset.sum_sub_distrib, mul_comm]
    rw [he]
    linarith only [hb]
  have hpoint : ∀ v ∈ T, ((hits G S v : ℝ) - a) * z v ≤
      if v ∈ U then t * ((hits G S v : ℝ) - a) else 0 := by
    intro v hv
    by_cases hu : v ∈ U
    · rw [if_pos hu]
      have hp : 0 ≤ (hits G S v : ℝ) - a :=
        sub_nonneg.mpr (Finset.mem_filter.mp hu).2.le
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcap v hv) hp
    · rw [if_neg hu]
      have hn : (hits G S v : ℝ) ≤ a := by
        by_contra hn
        exact hu (Finset.mem_filter.mpr ⟨hv, lt_of_not_ge hn⟩)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) (hz v hv)
  have hguard : (∑ v ∈ T, if v ∈ U then t * ((hits G S v : ℝ) - a) else 0) =
      ∑ v ∈ U, t * ((hits G S v : ℝ) - a) := by
    change _ = ∑ v ∈ T.filter (fun v => a < (hits G S v : ℝ)), _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [U, Finset.mem_filter, hv, true_and]
  have hs := Finset.sum_le_sum hpoint
  rw [hguard, ← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left hexcess ht
  have he : (∑ v ∈ T, (hits G S v : ℝ) * z v) =
      a * (∑ v ∈ T, z v) + ∑ v ∈ T, ((hits G S v : ℝ) - a) * z v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [incidence_sum G S T z, he]
  nlinarith only [hs, hb]

end Paper.Density.NeighborhoodSlack

#print axioms Paper.Density.NeighborhoodSlack.incidence_sum
#print axioms Paper.Density.NeighborhoodSlack.unweighted_incidence_le
#print axioms Paper.Density.NeighborhoodSlack.weighted_incidence_le
