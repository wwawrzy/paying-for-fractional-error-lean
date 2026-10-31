import Paper.Partitions.Local.SmallCutPartition

/-! The part-size parameter depends only on C, degree and the requested
cut accuracy, uniformly for every actual induced region. -/
namespace Paper.PartitionParameters

theorem exists_size (C : ℝ) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((4 * (Δ : ℝ) * C / ε) ^ 2))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkNat : 0 < k := by exact_mod_cast hkpos
  have hb : (4 * (Δ : ℝ) * C / ε) ^ 2 ≤ k := (le_max_right _ _).trans hk.le
  have hr := Real.le_sqrt_of_sq_le hb
  have hm := mul_le_mul_of_nonneg_left hr hε.le
  have he : ε * (4 * (Δ : ℝ) * C / ε) = 4 * Δ * C := by field_simp
  refine ⟨k, hkNat, (div_le_iff₀ (Real.sqrt_pos.mpr hkpos)).mpr ?_⟩
  nlinarith

end Paper.PartitionParameters
