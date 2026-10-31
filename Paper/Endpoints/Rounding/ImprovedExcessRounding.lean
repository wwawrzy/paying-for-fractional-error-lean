import Paper.Endpoints.Rounding.ImprovedExcessBounds
import Paper.Endpoints.Rounding.ImprovedExcessParameters

/-! The exact cardinality conclusion of `fv:imp:lemma` for its unfiltered
first set, arbitrary admissible chosen gain (including zero), and excess.
The real parameter statement includes every rational paper instance. -/
namespace Paper.ImprovedExcess
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem output_bound (a θ μ η : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hμ : 0 ≤ μ) (hμθ : μ ≤ θ) (hη : 0 ≤ η)
    (hadm : (μ + 1) * (μ + 1 - θ) ≤ (2 * a + 1) * (1 - θ) / a)
    (k : ℕ) (heq : 2 * a = k + θ) (hden : DensityWithExcess G a η)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    ((output G k (threshold a θ μ) x).card : ℝ) ≤
      (2 * a + 1 - μ) * (∑ v, x v) + 2 * η * threshold a θ μ * (1 + μ / (1 - θ)) := by
  let σ := threshold a θ μ
  obtain ⟨ht, hcW, hcL, hcZ, hcP⟩ := coefficients ha hθ hθ1 hμ hμθ hadm
  have hs := saving G k σ x a θ η (by linarith) heq hθ1 ht.le hden hx
  have hm := mass_bound G k σ x a θ η heq hθ hθ1 ht.le hden hx.1 hcap
  have hP := slack_nonneg G k σ x a θ heq hθ hx.1
  have hw := mul_le_mul_of_nonneg_right hcW (Nat.cast_nonneg (first G k σ x).card)
  have hl := mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg (middle G k σ x).card)
  have hz := mul_le_mul_of_nonneg_right hcZ (Nat.cast_nonneg (outside G k σ x).card)
  have hp := mul_le_mul_of_nonneg_right hcP hP
  have hmass : μ * (∑ v, x v) ≤ μ * (first G k σ x).card +
      (μ * σ * a / (1 - θ)) * (middle G k σ x).card -
      (μ * σ * (a + 1) / (1 - θ)) * (outside G k σ x).card +
      (μ / θ) * slack G k σ x a + 2 * η * μ * σ / (1 - θ) := by
    calc
      _ ≤ μ * ((first G k σ x).card + σ * a / (1 - θ) * (middle G k σ x).card -
        σ * (a + 1) / (1 - θ) * (outside G k σ x).card + slack G k σ x a / θ +
        2 * η * σ / (1 - θ)) := mul_le_mul_of_nonneg_left hm hμ
      _ = _ := by ring
  have hadd : 2 * η * μ * σ / (1 - θ) + 2 * η * σ =
      2 * η * σ * (1 + μ / (1 - θ)) := by ring
  dsimp only [σ] at hs hmass hadd ⊢
  linarith [hη]

/-- Domination is unconditional; the bound has exactly the paper's
threshold and additive term, with no degree guard in the first set. -/
theorem improved_rounding (a θ μ η : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hμ : 0 ≤ μ) (hμθ : μ ≤ θ) (hη : 0 ≤ η)
    (hadm : (μ + 1) * (μ + 1 - θ) ≤ (2 * a + 1) * (1 - θ) / a)
    (k : ℕ) (heq : 2 * a = k + θ) (hden : DensityWithExcess G a η)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    dominates G (output G k (threshold a θ μ) x) ∧
      ((output G k (threshold a θ μ) x).card : ℝ) ≤
        (2 * a + 1 - μ) * (∑ v, x v) + additive a θ μ η :=
  ⟨output_dominates G k (threshold a θ μ) x,
    output_bound G a θ μ η ha hθ hθ1 hμ hμθ hη hadm k heq hden x hx hcap⟩

/-- The paper's stated zero-excess consequence keeps the chosen gain. -/
theorem output_bound_no_excess (a θ μ : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hμ : 0 ≤ μ) (hμθ : μ ≤ θ)
    (hadm : (μ + 1) * (μ + 1 - θ) ≤ (2 * a + 1) * (1 - θ) / a)
    (k : ℕ) (heq : 2 * a = k + θ) (hden : Incidence.InducedDensityBound G a)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    ((output G k (threshold a θ μ) x).card : ℝ) ≤ (2 * a + 1 - μ) * (∑ v, x v) := by
  have hd : DensityWithExcess G a 0 := by
    intro S
    simpa only [add_zero] using hden S
  simpa only [mul_zero, zero_mul, add_zero] using
    output_bound G a θ μ 0 ha hθ hθ1 hμ hμθ le_rfl hadm k heq hd x hx hcap

end Paper.ImprovedExcess
#print axioms Paper.ImprovedExcess.output_bound
#print axioms Paper.ImprovedExcess.improved_rounding
#print axioms Paper.ImprovedExcess.output_bound_no_excess
