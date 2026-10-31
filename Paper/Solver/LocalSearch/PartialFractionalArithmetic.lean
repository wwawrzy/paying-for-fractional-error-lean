import Paper.Solver.LocalSearch.PartialFractionalProgram

namespace Paper.PartialFractionalArithmetic
variable {V : Type} [LinearOrder V]

theorem value (Δ k Q T s q : ℕ) (hQ : 0 < Q) (hq : 0 < q)
    (env : OwnerVirtualPrepare.Env V) (pn tn : ℕ) :
    (PartialFractionalProgram.numerator Δ k Q T s q env pn tn : ℝ) /
      PartialFractionalProgram.denominator Δ k Q T s q =
        (env.metadata.heavy.toNat : ℝ) + ((env.metadata.center && env.high).toNat : ℝ) +
          (pn : ℝ) / OwnerBoundaryMean.denominator Δ k Q T +
          (tn : ℝ) / OwnerRoleNumerator.denominator Δ k Q T s q := by
  have ht : (OwnerRoleNumerator.denominator Δ k Q T s q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (OwnerRoleNumerator.denominator_pos Δ k Q T s q hQ hq)
  have hb : (OwnerBoundaryMean.denominator Δ k Q T : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (OwnerBoundaryMean.denominator_pos Δ k Q T hQ)
  unfold PartialFractionalProgram.numerator PartialFractionalProgram.repairs PartialFractionalProgram.denominator
  push_cast
  field_simp

end Paper.PartialFractionalArithmetic
