import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
set_option maxHeartbeats 200000
namespace Paper.AbsorptionPublicParameters

theorem public_absorption_parameters
    (r epsilon : Real) (q : Nat) (hr : 1 ≤ r) (hepsilon : 0 < epsilon) :
    ∃ delta : Rat, 0 < delta ∧ (delta : Real) ≤ epsilon / (2 * r) ∧
      1 ≤ max 1 (Nat.ceil (2 * (q : Real) / epsilon)) ∧
      2 * (q : Real) / epsilon ≤
        ((max 1 (Nat.ceil (2 * (q : Real) / epsilon)) : Nat) : Real) := by
  have hden : 0 < 2 * r := by linarith
  obtain ⟨delta, hdelta, hsmall⟩ := exists_rat_btwn (div_pos hepsilon hden)
  refine ⟨delta, ?_, hsmall.le, le_max_left _ _, ?_⟩
  · exact_mod_cast hdelta
  · apply (Nat.le_ceil (2 * (q : Real) / epsilon)).trans
    exact_mod_cast (le_max_right 1 (Nat.ceil (2 * (q : Real) / epsilon)))

end Paper.AbsorptionPublicParameters

#print axioms Paper.AbsorptionPublicParameters.public_absorption_parameters
