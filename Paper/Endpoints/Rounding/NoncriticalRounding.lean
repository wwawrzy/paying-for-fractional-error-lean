import Paper.Endpoints.Rounding.NoncriticalSaving
import Paper.Endpoints.Rounding.NoncriticalParameters

/-! The genuine graph counting bounds imply strict saving at every
noninteger critical density. No saving/mass inequality is assumed. -/
namespace Paper.NoncriticalRounding
open SevenFoundation NoncriticalGeometry NoncriticalCounting NoncriticalExcess NoncriticalMass
open NoncriticalParameters
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem strict_bound (a θ : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (k : ℕ) (heq : 2 * a = k + θ) (hden : Incidence.InducedDensityBound G a)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    ((NoncriticalGeometry.output G k (threshold a θ) x).card : ℝ) ≤
      (2 * a + 1 - gain θ) * ∑ v, x v := by
  let σ := threshold a θ
  let μ := gain θ
  obtain ⟨hμ, _, hσ, hcW, hcL, hcZ, hcP⟩ := coefficients ha hθ hθ1
  have hs := NoncriticalSaving.saving G k σ x a θ (by linarith) heq hθ1 hσ hden hx
  have hm := mass_bound G k σ x a θ heq hθ hθ1 hσ hden hx.1 hcap
  have hP : 0 ≤ slack G k σ x a := by
    have hp := low_mass G k σ x a θ heq hx.1
    have hsum : 0 ≤ ∑ v ∈ low G k σ x, x v := Finset.sum_nonneg (fun v _ => hx.1 v)
    exact (mul_nonneg (le_of_lt hθ) hsum).trans hp
  have hw := mul_le_mul_of_nonneg_right hcW (Nat.cast_nonneg (first G k σ x).card)
  have hl := mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg (middle G k σ x).card)
  have hz := mul_le_mul_of_nonneg_right hcZ (Nat.cast_nonneg (outside G k σ x).card)
  have hp := mul_le_mul_of_nonneg_right hcP hP
  have hmass : μ * (∑ v, x v) ≤ μ * (first G k σ x).card +
      (μ * σ * a / (1 - θ)) * (middle G k σ x).card -
      (μ * σ * (a + 1) / (1 - θ)) * (outside G k σ x).card +
      (μ / θ) * slack G k σ x a := by
    calc
      _ ≤ μ * ((first G k σ x).card + σ * a / (1 - θ) * (middle G k σ x).card -
        σ * (a + 1) / (1 - θ) * (outside G k σ x).card + slack G k σ x a / θ) :=
          mul_le_mul_of_nonneg_left hm (le_of_lt hμ)
      _ = _ := by ring
  dsimp only [σ, μ] at hs hmass ⊢
  linarith

theorem error_cancellation (a θ : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < gain θ / (2 * a + 1 - gain θ) ∧
      (2 * a + 1 - gain θ) * (1 + gain θ / (2 * a + 1 - gain θ)) = 2 * a + 1 := by
  obtain ⟨hp, hb, _⟩ := coefficients ha hθ hθ1
  have hn : 0 < 2 * a + 1 - gain θ := by linarith
  refine ⟨div_pos hp hn, ?_⟩
  field_simp <;> ring

end Paper.NoncriticalRounding
