import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
/-! Numerical composition for the corrected `fv:imp:absorb` (r >= 1).
This module does not construct or certify a distributed covering algorithm. -/

set_option maxHeartbeats 200000
namespace Paper.AdditiveAbsorptionArithmetic

theorem absorption_half_error
    (r epsilon delta : Real) (hr : 1 <= r)
    (hdelta : delta <= epsilon / (2 * r)) :
    r * delta <= epsilon / 2 := by
  have hden : 0 < 2 * r := by
    have hpos : 0 < r := by linarith
    nlinarith
  have hdelta' : delta * (2 * r) ≤ epsilon := (le_div_iff₀ hden).mp hdelta
  nlinarith

theorem absorption_bound
    (r epsilon delta tau opt q d d0 : Real) (K : Nat)
    (hr : 1 <= r)
    (hepsilon : 0 < epsilon)
    (hdelta_pos : 0 < delta)
    (hdelta : delta <= epsilon / (2 * r))
    (htau : 0 <= tau)
    (htauopt : tau <= opt)
    (hq : 0 <= q)
    (hd_nonneg : 0 <= d)
    (hd : d <= d0)
    (hd0 : d0 <= r * (1 + delta) * tau + q)
    (hthreshold : 2 * q / epsilon <= (K : Real))
    (hcases : d = opt ∨ (K : Real) < opt) :
    d <= (r + epsilon) * opt := by
  have hopt : 0 ≤ opt := htau.trans htauopt
  have hr0 : 0 ≤ r := by linarith
  rcases hcases with heq | hlarge
  · rw [heq]
    have hcoef : 1 ≤ r + epsilon := by linarith
    simpa using mul_le_mul_of_nonneg_right hcoef hopt
  · have hhalf := absorption_half_error r epsilon delta hr hdelta
    have herror := mul_le_mul_of_nonneg_right hhalf hopt
    have hthreshold' : 2 * q ≤ (K : Real) * epsilon :=
      (div_le_iff₀ hepsilon).mp hthreshold
    have hlarge' := mul_le_mul_of_nonneg_right (le_of_lt hlarge) (le_of_lt hepsilon)
    have hqbound : q ≤ epsilon / 2 * opt := by nlinarith
    have hcoef : 0 ≤ r * (1 + delta) :=
      mul_nonneg hr0 (by linarith)
    have hscale := mul_le_mul_of_nonneg_left htauopt hcoef
    nlinarith [hd.trans hd0]

end Paper.AdditiveAbsorptionArithmetic

#print axioms Paper.AdditiveAbsorptionArithmetic.absorption_half_error
#print axioms Paper.AdditiveAbsorptionArithmetic.absorption_bound
