import Paper.Solver.Density.CappedUniformParameters
import Paper.Solver.Density.CappedRoundComplexity

/-! Scalar identities and deadline bounds for the silent capped protocol. -/
namespace Paper.Density.CappedSilentParameters

/-- The rational update scale and threshold ratio are reciprocal for positive `m`. -/
theorem scale_mul_rho {m : ℕ} (hm : 0 < m) :
    CappedCounterState.scale m * CappedUniformParameters.rho m = 1 := by
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_mul, Rat.cast_one, CappedUniformParameters.scale_cast,
    CappedUniformParameters.rho_cast] using CappedGrowth.factor_mul_rho hm

/-- One initialization round and complete six-round cycles satisfy the
paper's logarithmic square bound, also for degrees zero and one. -/
theorem silent_rounds_bound (m Delta : ℕ) :
    1 + 6 * (CappedGrowth.timeBound m Delta + 1) ≤
      (6*m+7) * (1 + (Nat.clog 2 (max 2 Delta))^2) := by
  have h := CappedRoundComplexity.rounds_bound m Delta
  nlinarith

end Paper.Density.CappedSilentParameters

#print axioms Paper.Density.CappedSilentParameters.scale_mul_rho
#print axioms Paper.Density.CappedSilentParameters.silent_rounds_bound
