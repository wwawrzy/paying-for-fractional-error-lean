import Paper.TotalDomination.CostSaving

namespace Paper.TotalDomination
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (I : Input G)

theorem neighbor_mass_le (S T : Finset V) (hT : T ⊆ neighbors G S)
    (hx : ∀ v, 0 ≤ I.x v) :
    (∑ v ∈ T, I.x v) ≤ ∑ r ∈ S, ∑ v ∈ G.neighborFinset r, I.x v := by
  classical
  rw [open_incidence_sum]
  calc
    _ ≤ ∑ v ∈ T, ((G.neighborFinset v ∩ S).card : ℝ)*I.x v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨r,hr,ha⟩ := (mem_neighbors G).mp (hT hv)
      have hp : 0 < (G.neighborFinset v ∩ S).card := Finset.card_pos.mpr
        ⟨r,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v r).mpr ha,hr⟩⟩
      have hpR : (1:ℝ) ≤ (G.neighborFinset v ∩ S).card := by exact_mod_cast hp
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpR (hx v)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => mul_nonneg (Nat.cast_nonneg _) (hx v))

theorem residual_rows_bound (S : Finset V) (hS : S ⊆ residual G I)
    (hcover : ∀ r ∈ I.demands, 1 ≤ ∑ v ∈ G.neighborFinset r, I.x v) :
    (∑ r ∈ S, ∑ v ∈ G.neighborFinset r, I.x v) ≤ (S.card : ℝ)+oversupply G I := by
  have hsum : (∑ r ∈ S, ((∑ v ∈ G.neighborFinset r, I.x v)-1)) ≤ oversupply G I := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro r hr _
    exact sub_nonneg.mpr (hcover r (Finset.mem_sdiff.mp hr).1)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hsum
  linarith

theorem mass_le_card_add_oversupply (S T : Finset V)
    (hS : S ⊆ residual G I) (hT : T ⊆ neighbors G S)
    (hx : ∀ v, 0 ≤ I.x v)
    (hcover : ∀ r ∈ I.demands, 1 ≤ ∑ v ∈ G.neighborFinset r, I.x v) :
    (∑ v ∈ T, I.x v) ≤ (S.card : ℝ)+oversupply G I :=
  (neighbor_mass_le G I S T hT hx).trans (residual_rows_bound G I S hS hcover)

end Paper.TotalDomination
#print axioms Paper.TotalDomination.mass_le_card_add_oversupply
