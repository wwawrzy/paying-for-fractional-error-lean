import GraphTheory.Local.LocalCyclesRamseyReservoir
import Paper.Partitions.Local.DeterministicColorReductionIdentifiers

/-! Quantitative inversion of the finite Ramsey reservoir used on the original
identifier alphabet. The rank may depend on the cycle order. -/
namespace Paper.CycleRamseyLogStar

open LocalCyclesRamseyReservoir DeterministicColorReductionLogStar
  DeterministicColorReductionIdentifiers

theorem reservoir_step_bound (m : ℕ) :
    (2 ^ (2 ^ m) + 1) ^ m ≤ 2 ^ (2 ^ (2 * m + 1)) := by
  have hm : m ≤ 2 ^ m := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hbase : 2 ^ (2 ^ m) + 1 ≤ 2 ^ (2 ^ m + 1) := by
    rw [Nat.pow_succ]
    have hp : 0 < 2 ^ (2 ^ m) := by positivity
    omega
  have hexp : (2 ^ m + 1) * m ≤ 2 ^ (2 * m + 1) := by
    calc
      _ ≤ (2 ^ m + 2 ^ m) * 2 ^ m :=
        Nat.mul_le_mul (by
          have hp : 0 < 2 ^ m := by positivity
          omega) hm
      _ = 2 ^ (2 * m + 1) := by
        rw [show 2 * m + 1 = (m + 1) + m by omega, Nat.pow_add, Nat.pow_succ]
        ring
  calc
    _ ≤ (2 ^ (2 ^ m + 1)) ^ m := Nat.pow_le_pow_left hbase m
    _ = 2 ^ ((2 ^ m + 1) * m) := by rw [Nat.pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

theorem reservoir_step_logStar (m : ℕ) :
    logStar ((2 ^ (2 ^ m) + 1) ^ m) ≤ logStar m + 4 := by
  have h0 := logStar_mono (reservoir_step_bound m)
  have h1 := logStar_pow (2 ^ (2 * m + 1))
  have h2 := logStar_pow (2 * m + 1)
  have h3 := logStar_mono (show 2 * m + 1 ≤ 2 * (m + 1) by omega)
  have h4 := logStar_double (m + 1)
  have h5 := logStar_succ m
  omega

theorem reservoir_logStar (k L : ℕ) :
    logStar (ramseyBound 2 k L) ≤ 4 * k + logStar L + 2 := by
  induction k generalizing L with
  | zero =>
    have h0 := logStar_mono (show 2 * (L - 1) + 1 ≤ 2 * (L + 1) by omega)
    have h1 := logStar_double (L + 1)
    have h2 := logStar_succ L
    simpa only [ramseyBound, Nat.mul_zero, Nat.zero_add] using
      (show logStar (2 * (L - 1) + 1) ≤ logStar L + 2 by omega)
  | succ k ih =>
    have h0 := reservoir_step_logStar (ramseyBound 2 k (L - 1))
    have h1 := ih (L - 1)
    have h2 := logStar_mono (show L - 1 ≤ L by omega)
    change logStar ((2 ^ (2 ^ ramseyBound 2 k (L - 1)) + 1) ^
      ramseyBound 2 k (L - 1)) ≤ _
    omega

theorem logStar_le_self (n : ℕ) : logStar n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 1
    · rw [logStar_small n hn]
      omega
    · rw [logStar_step n (by omega)]
      have hlt := clog_lt_self n (by omega)
      have hh := ih _ hlt
      omega

theorem reservoir_positive (k L : ℕ) : 0 < ramseyBound 2 k L := by
  cases k with
  | zero => simp only [ramseyBound]; omega
  | succ k => simp only [ramseyBound]; positivity

/-- This is the direction needed by the lower bound: an upper bound on the
cycle order by the rank-dependent reservoir bounds logStar(order) by the rank. -/
theorem order_logStar (N r : ℕ)
    (hN : N < 4 * ramseyBound 2 (2 * r) (8 * r + 8) + 32) :
    logStar N ≤ 16 * r + 46 := by
  let R := ramseyBound 2 (2 * r) (8 * r + 8)
  have hR : 1 ≤ R := reservoir_positive _ _
  have hNR : N ≤ 36 * R := by omega
  have h0 := logStar_mono hNR
  have h1 := logStar_mul_bound 36 R
  have h2 := reservoir_logStar (2 * r) (8 * r + 8)
  have h3 := logStar_le_self (8 * r + 8)
  dsimp only [R] at *
  omega

end Paper.CycleRamseyLogStar

#print axioms Paper.CycleRamseyLogStar.reservoir_step_bound
#print axioms Paper.CycleRamseyLogStar.reservoir_logStar
#print axioms Paper.CycleRamseyLogStar.order_logStar
