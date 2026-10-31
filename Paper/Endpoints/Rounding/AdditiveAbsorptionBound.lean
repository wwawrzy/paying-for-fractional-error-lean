import Paper.Endpoints.Rounding.AdditiveAbsorptionArithmetic

/-! Numerical compatibility helper for the corrected r >= 1 absorption statement. -/

namespace Paper.AdditiveAbsorptionBound

variable (r ε δ τ opt q d d0 : ℝ) (K : ℕ)
variable (h1 : 1 ≤ r)
variable (h2 : 0 < ε)
variable (h3 : 0 < δ)
variable (h4 : δ ≤ ε / (2 * r))
variable (h5 : 0 ≤ τ)
variable (h6 : τ ≤ opt)
variable (h7 : 0 ≤ q)
variable (h8 : 0 ≤ d)
variable (h9 : d ≤ d0)
variable (h10 : d0 ≤ r * (1 + δ) * τ + q)
variable (h11 : 2 * q ≤ ε * K)
variable (h12 : d = opt ∨ (K : ℝ) < opt)

include h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 in
theorem main_bound : d ≤ (r + ε) * opt := by
  apply Paper.AdditiveAbsorptionArithmetic.absorption_bound r ε δ τ opt q d d0 K
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ?_ h12
  apply (div_le_iff₀ h2).mpr
  nlinarith [h11]

end Paper.AdditiveAbsorptionBound

#print axioms Paper.AdditiveAbsorptionBound.main_bound
