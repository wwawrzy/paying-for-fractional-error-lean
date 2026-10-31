import Paper.Endpoints.Rounding.SurfaceResidualBudget
import Mathlib.Tactic.Linarith

namespace Paper.SurfaceTwoBudget

/-- Slack absorbs the surface error once the rounded cover exceeds the budget.
This is an arithmetic lemma, not a runtime or a surface density certificate. -/
theorem large_cover (D tau e : ℝ)
    (hlarge : 1176 * e < D)
    (hround : (1 + 1 / 294 : ℝ) * D ≤ (1 + 1 / 588 : ℝ) * tau + 2 * e) :
    D ≤ tau := by
  linarith

/-- The two proof cases use the same output. No global branch is required by
this statement; a runtime still has to establish the component hypotheses. -/
theorem two_budgets (F D₀ D₁ optUnit tau gamma gammaFrac e : ℝ)
    (hreplace : D₁ ≤ D₀)
    (hintegral : F + optUnit ≤ 7 * gamma)
    (hfractional : F + tau ≤ 7 * gammaFrac)
    (hbenchmark : gammaFrac ≤ gamma)
    (hround : (1 + 1 / 294 : ℝ) * D₀ ≤ (1 + 1 / 588 : ℝ) * tau + 2 * e)
    (hcases : D₁ = optUnit ∨ 1176 * e < D₀) :
    F + D₁ ≤ 7 * gamma := by
  rcases hcases with hsolved | hlarge
  · simpa only [hsolved] using hintegral
  · have h := large_cover D₀ tau e hlarge hround
    linarith

end Paper.SurfaceTwoBudget
