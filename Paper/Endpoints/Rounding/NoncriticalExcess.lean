import Paper.Endpoints.Rounding.NoncriticalCounting

namespace Paper.NoncriticalExcess
open SevenFoundation NoncriticalGeometry NoncriticalCounting
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

noncomputable def excess (a : ℝ) : ℝ := ∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1))

theorem excess_le (a : ℝ) (hden : Incidence.InducedDensityBound G a) :
    excess G k σ x a ≤ a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card := by
  classical
  have hinc := Incidence.closed_incidence_le_of_density G hden
    (high G k σ x) (residual G k σ x ∩ covered G (high G k σ x))
  have hsum : (∑ v ∈ high G k σ x,
      ((closed G v ∩ (residual G k σ x ∩ covered G (high G k σ x))).card : ℝ)) =
      ∑ v ∈ high G k σ x, (hits G k σ x v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have heq : closed G v ∩ (residual G k σ x ∩ covered G (high G k σ x)) =
        closed G v ∩ residual G k σ x := by
      ext r
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hc, hr, _⟩
        exact ⟨hc, hr⟩
      · rintro ⟨hc, hr⟩
        exact ⟨hc, hr, Finset.mem_biUnion.mpr ⟨v, hv, hc⟩⟩
    rw [heq]
    rfl
  rw [hsum, covered_inter_high, covered_union_high,
    Finset.card_union_of_disjoint (high_middle_disjoint G k σ x)] at hinc
  have hcard : ((high G k σ x).card : ℝ) =
      (overlap G k σ x).card + (outside G k σ x).card := by
    exact_mod_cast high_card_split G k σ x
  have he : excess G k σ x a = (∑ v ∈ high G k σ x, (hits G k σ x v : ℝ)) -
      (2 * a + 1 : ℝ) * (high G k σ x).card := by
    simp [excess, Finset.sum_sub_distrib, mul_comm]
    ring
  push_cast at hinc he
  rw [hcard] at he
  rw [hcard] at hinc
  rw [he]
  nlinarith

theorem excess_lower (a θ : ℝ) (heq : 2 * a = k + θ) :
    (1 - θ) * (high G k σ x).card ≤ excess G k σ x a := by
  calc
    _ = ∑ _v ∈ high G k σ x, (1 - θ) := by simp [mul_comm]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      have hh : ((k + 2 : ℕ) : ℝ) ≤ hits G k σ x v := by
        exact_mod_cast (Finset.mem_filter.mp hv).2
      push_cast at hh
      linarith

theorem weighted_excess (a θ : ℝ) (heq : 2 * a = k + θ) (hθ : θ < 1) :
    (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) ≤
      σ * excess G k σ x a := by
  rw [excess, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hh : ((k + 2 : ℕ) : ℝ) ≤ hits G k σ x v := by
    exact_mod_cast (Finset.mem_filter.mp hv).2
  push_cast at hh
  have hn : 0 ≤ (hits G k σ x v : ℝ) - (2 * a + 1) := by linarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (high_weight G k σ x hv) hn

end Paper.NoncriticalExcess
