import Paper.Endpoints.Rounding.NoncriticalMass
import Paper.Endpoints.Rounding.WeightedBudget
import Paper.Certificates.Counting.PartialOptimum

namespace Paper.NoncriticalSaving
open SevenFoundation NoncriticalGeometry NoncriticalCounting NoncriticalExcess NoncriticalMass
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

theorem cost_decomposition (a : ℝ) :
    (2 * a + 1) * (∑ v, x v) = (2 * a + 1) * (∑ v ∈ first G k σ x, x v) +
      (∑ v, (hits G k σ x v : ℝ) * x v) + slack G k σ x a -
      (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) := by
  have hw : (2 * a + 1) * (∑ v ∈ first G k σ x, x v) =
      ∑ v, if v ∈ first G k σ x then (2 * a + 1) * x v else 0 := by simp [Finset.mul_sum]
  have hp : slack G k σ x a = ∑ v, if v ∈ low G k σ x then
      ((2 * a + 1) - (hits G k σ x v : ℝ)) * x v else 0 := by simp [slack]
  have he : (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) =
      ∑ v, if v ∈ high G k σ x then ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v else 0 := by simp
  rw [hw, hp, he, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hW : v ∈ first G k σ x
  · have hH : v ∉ high G k σ x := fun h => Finset.disjoint_left.mp (high_disjoint_first G k σ x) h hW
    have hL : v ∉ low G k σ x := fun h => low_not_first G k σ x h hW
    simp only [if_pos hW, if_neg hH, if_neg hL, first_hits_zero G k σ x hW,
      Nat.cast_zero, zero_mul, add_zero, sub_zero]
  · rw [if_neg hW]
    by_cases hH : v ∈ high G k σ x
    · have hL : v ∉ low G k σ x := fun h => Finset.disjoint_left.mp (high_low_disjoint G k σ x) hH h
      rw [if_pos hH, if_neg hL]
      ring
    · rw [if_neg hH, if_pos (low_of_not G k σ x hW hH)]
      ring

theorem residual_coverage (hx : PartialOptimum.Feasible G Finset.univ x) :
    ((residual G k σ x).card : ℝ) ≤ ∑ v, (hits G k σ x v : ℝ) * x v := by
  change ((residual G k σ x).card : ℝ) ≤ ∑ v, ((closed G v ∩ residual G k σ x).card : ℝ) * x v
  rw [← WeightedBudget.incidence_sum]
  calc
    _ = ∑ _r ∈ residual G k σ x, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun r _ => hx.2 r (Finset.mem_univ _))

theorem saving (a θ : ℝ) (ha : 0 ≤ a) (heq : 2 * a = k + θ) (hθ : θ < 1)
    (hσ : 0 ≤ σ) (hden : Incidence.InducedDensityBound G a)
    (hx : PartialOptimum.Feasible G Finset.univ x) :
    ((2 * a + 1) * σ - 1) * (first G k σ x).card +
      (1 - a * σ) * (middle G k σ x).card +
      ((a + 1) * σ - 1) * (outside G k σ x).card + slack G k σ x a ≤
        (2 * a + 1) * (∑ v, x v) - (NoncriticalGeometry.output G k σ x).card := by
  have hw := mul_le_mul_of_nonneg_left (first_mass_lower G k σ x)
    (show (0 : ℝ) ≤ 2 * a + 1 by linarith)
  have hr := residual_coverage G k σ x hx
  have he := weighted_excess G k σ x a θ heq hθ
  have hi := mul_le_mul_of_nonneg_left (excess_le G k σ x a hden) hσ
  have hc := cost_decomposition G k σ x a
  have hcard := output_card_identity G k σ x
  nlinarith

end Paper.NoncriticalSaving
