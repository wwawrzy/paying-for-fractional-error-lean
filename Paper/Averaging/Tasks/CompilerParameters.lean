import Paper.Owners.Construction.OwnerCompilerBound

/-! Parameter-only accuracy choice for the actually proved, coarser owner
density constant. No graph order or optimum occurs in these parameters. -/
namespace Paper.CompilerParameters

theorem exists_parameters (a : ℕ) (ha : 1 ≤ a) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ L Δ : ℕ, ∃ ξ η : ℝ, 4 * (a : ℝ) ≤ L ∧ 1 ≤ Δ ∧ 0 < ξ ∧ 0 < η ∧
      ξ + B * K * OwnerCompilerBound.factor a L Δ η ≤ δ := by
  let M := B * K
  have hM : 0 ≤ M := mul_nonneg hB hK
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨L, hL⟩ := exists_nat_gt (max (4 * (a : ℝ)) (16 * (a : ℝ) * M / δ))
  have hLlower : 4 * (a : ℝ) ≤ L := (le_max_left _ _).trans hL.le
  have hLpos : (0 : ℝ) < L := by linarith
  have hLmul : 16 * (a : ℝ) * M < (L : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hL)
  have hLbudget : M * (2 * (a : ℝ) / L) ≤ δ / 8 := by
    have h : 2 * (a : ℝ) * M / L ≤ δ / 8 := (div_le_iff₀ hLpos).mpr (by nlinarith)
    convert h using 1 <;> ring
  let C := (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4
  obtain ⟨Δ, hΔ⟩ := exists_nat_gt (max (1 : ℝ) (16 * C * M / δ))
  have hΔ1 : (1 : ℝ) < Δ := (le_max_left _ _).trans_lt hΔ
  have hΔNat : 1 ≤ Δ := by
    have hh : (0 : ℝ) < Δ := by linarith
    have hhNat : 0 < Δ := by exact_mod_cast hh
    omega
  have hΔmul : 16 * C * M < (Δ : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hΔ)
  have hΔbudget : M * (2 * C / Δ) ≤ δ / 8 := by
    have h : 2 * C * M / Δ ≤ δ / 8 := (div_le_iff₀ (by linarith : (0 : ℝ) < Δ)).mpr (by nlinarith)
    convert h using 1 <;> ring
  let η := δ / (16 * (M + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηeq : 16 * (M + 1) * η = δ := by
    dsimp only [η]
    field_simp [show M + 1 ≠ 0 by linarith]
  have hηbudget : M * (2 * η) ≤ δ / 8 := by nlinarith
  let ξ := δ / 4
  have hξ : 0 < ξ := by dsimp only [ξ]; positivity
  refine ⟨L, Δ, ξ, η, hLlower, hΔNat, hξ, hη, ?_⟩
  change ξ + M * OwnerCompilerBound.factor a L Δ η ≤ δ
  dsimp only [OwnerCompilerBound.factor]
  change ξ + M * (2 * (a : ℝ) / L + 2 * C / Δ + 2 * η) ≤ δ
  dsimp only [ξ]
  nlinarith
end Paper.CompilerParameters
