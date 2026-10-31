import Paper.Solver.Density.RationalRuntime

/-! Explicit polynomial-time/short-message parameters for the rational
bounded-degree execution. This is a resource lemma, not an accuracy or
termination contract for a fractional solver. -/
namespace Paper.Density.RationalParameters
open RationalRuntime

theorem message_linear (m K : ℕ) :
    messageBound m K ≤ (2 * Nat.clog 2 (m + 2) + 5) * (K + 1) := by
  let c := Nat.clog 2 (m + 2)
  have hm : m + 2 ≤ 2 ^ c := Nat.le_pow_clog (by decide) _
  have hK : K + 1 ≤ 2 ^ K := K.lt_two_pow_self
  have hD : denominator m K ≤ 2 ^ (c * K) := by
    unfold denominator
    calc
      _ ≤ (2 ^ c) ^ K := Nat.pow_le_pow_left (by omega : m + 1 ≤ 2 ^ c) K
      _ = _ := (pow_mul _ _ _).symm
  have hDpos : 0 < denominator m K := by unfold denominator; positivity
  have hDlog : Nat.clog 2 (denominator m K + 2) ≤ c * K + 2 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    norm_num
    omega
  have hF : target m K + 2 ≤ 2 ^ (c + K) := by
    unfold target
    calc
      _ ≤ (m + 2) * (K + 1) := by nlinarith
      _ ≤ 2 ^ c * 2 ^ K := Nat.mul_le_mul hm hK
      _ = _ := (pow_add _ _ _).symm
  have hFlog := Nat.clog_le_of_le_pow hF
  change max (2 * Nat.clog 2 (target m K + 2) + 1)
    (2 * Nat.clog 2 (denominator m K + 2)) ≤ _
  apply max_le <;> dsimp only [c] at * <;> nlinarith

theorem rounds_quadratic {V : Type} [DecidableEq V] (m K : ℕ) :
    (program (V := V) m K).rounds ≤ 4 * m * (m + 1) * (K + 1) ^ 2 := by
  rw [rounds]
  have houter : K + target m K ≤ (m + 1) * (K + 1) := by unfold target; nlinarith
  calc
    _ ≤ ((m + 1) * (K + 1)) * (2 * m) * (2 * (K + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ houter) (by omega)
    _ = _ := by ring

theorem fifth_power_le (x : ℝ) (hx : 0 ≤ x) (h1 : x ≤ 1) :
    (1 + x) ^ 5 ≤ 1 + 31 * x := by
  have hp (j : ℕ) : x ^ (j + 1) ≤ x := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ hx h1 : x ^ j ≤ 1) hx
  have h2 : x ^ 2 ≤ x := hp 1
  have h3 : x ^ 3 ≤ x := hp 2
  have h4 : x ^ 4 ≤ x := hp 3
  have h5 : x ^ 5 ≤ x := hp 4
  calc
    _ = 1 + 5 * x + 10 * x ^ 2 + 10 * x ^ 3 + 5 * x ^ 4 + x ^ 5 := by ring
    _ ≤ _ := by linarith only [h2, h3, h4, h5]

theorem public_accuracy (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (31 / δ)
  have hmp : (0 : ℝ) < m := (by positivity : (0 : ℝ) < 31 / δ).trans hm
  have hm1 : 1 ≤ m := by exact_mod_cast (Nat.pos_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hmp))
  have hrec : 1 / (m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmp).mpr
    simpa using (show (1 : ℝ) ≤ m by exact_mod_cast hm1)
  have herror : 31 / (m : ℝ) ≤ δ := by
    apply (div_le_iff₀ hmp).mpr
    have hh := (div_lt_iff₀ hδ).mp hm
    linarith
  refine ⟨m, hm1, ?_⟩
  have hf := fifth_power_le (1 / (m : ℝ)) (by positivity) hrec
  have he : 31 * (1 / (m : ℝ)) = 31 / (m : ℝ) := by ring
  linarith

end Paper.Density.RationalParameters

#print axioms Paper.Density.RationalParameters.message_linear
#print axioms Paper.Density.RationalParameters.rounds_quadratic
#print axioms Paper.Density.RationalParameters.public_accuracy
