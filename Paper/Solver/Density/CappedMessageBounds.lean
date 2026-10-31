import Paper.Communication.PrefixCode
import Paper.Solver.Density.CappedGrowth

/-! Explicit bit bounds for local denominator/exponent packets. The vertex
count and degree are analysis variables only; PrefixCode.counters uses neither. -/
namespace Paper.Density.CappedMessageBounds

private theorem succ_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem exponent_log_bound (n : ℕ) : Nat.clog 2 (n+1) ≤ n :=
  Nat.clog_le_of_le_pow (succ_le_two_pow n)

theorem logarithmic_packets (m Delta vertices extra den exponent : ℕ) (flag : Bool)
    (hdegree : Delta ≤ vertices) (hden : den ≤ Delta+1)
    (hexponent : exponent ≤ CappedGrowth.timeBound m Delta + extra) :
    (PrefixCode.counters.encode (den,exponent,flag)).length ≤
      (2*m+2*extra+5) * Nat.clog 2 (vertices+2) := by
  let H := Nat.clog 2 (vertices+2)
  have hH : 1 ≤ H := Nat.clog_pos (by decide) (by omega)
  have hd : Nat.clog 2 (den+1) ≤ H := Nat.clog_mono_right 2 (by omega)
  have hD : Nat.clog 2 (Delta+1) ≤ H := Nat.clog_mono_right 2 (by omega)
  have he : exponent ≤ m*H+extra := by
    have hh := Nat.mul_le_mul_left m hD
    unfold CappedGrowth.timeBound at hexponent
    omega
  have heLog := exponent_log_bound exponent
  have hbits := PrefixCode.counters_length den exponent flag
  have hpad : 2*extra+3 ≤ (2*extra+3)*H := Nat.le_mul_of_pos_right _ hH
  nlinarith

end Paper.Density.CappedMessageBounds
#print axioms Paper.Density.CappedMessageBounds.logarithmic_packets
