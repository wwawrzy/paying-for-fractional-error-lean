import Paper.Solver.Density.CappedGrowth

/-! Comparison of the explicit capped-protocol deadline with the logarithmic
square bound in the paper, including maximum degrees zero and one. -/
namespace Paper.Density.CappedRoundComplexity

theorem log_successor_bound (Delta : ℕ) :
    Nat.clog 2 (Delta+1) ≤ Nat.clog 2 (max 2 Delta)+1 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (max 2 Delta)
  have hD := le_max_right 2 Delta
  have h2 := le_max_left 2 Delta
  omega

/-- An explicit density-dependent constant for the paper's round bound. -/
theorem rounds_bound (m Delta : ℕ) :
    5 + 6 * CappedGrowth.timeBound m Delta ≤
      (6*m+5) * (1 + (Nat.clog 2 (max 2 Delta))^2) := by
  have hl := log_successor_bound Delta
  have hpos : 1 ≤ Nat.clog 2 (max 2 Delta) :=
    Nat.clog_pos (by decide) (by omega)
  have hsq : Nat.clog 2 (Delta+1) ≤ 1 + (Nat.clog 2 (max 2 Delta))^2 := by
    nlinarith
  have hh := Nat.mul_le_mul_left (6*m) hsq
  unfold CappedGrowth.timeBound
  nlinarith

end Paper.Density.CappedRoundComplexity
#print axioms Paper.Density.CappedRoundComplexity.rounds_bound
