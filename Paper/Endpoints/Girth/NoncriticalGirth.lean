import Paper.Endpoints.Girth.CurrentPlanarFaceBound
import Paper.Endpoints.Bounds.SeparateDensities
import Paper.Preliminaries.PlanarDensity

/-! # The noninteger girth cases, with the actual encoded endpoint -/

namespace Paper.NoncriticalGirth

open BroadcastModel SevenFoundation

def density (g : ℕ) : ℚ := (g : ℚ) / ((g : ℚ) - 2)

theorem density_bounds (g : ℕ) (hg : 3 ≤ g) : 1 ≤ density g ∧ density g ≤ 3 := by
  have hgQ : (3 : ℚ) ≤ g := by exact_mod_cast hg
  have hp : (0 : ℚ) < (g : ℚ) - 2 := by linarith
  constructor
  · rw [density, le_div_iff₀ hp]
    linarith
  · rw [density, div_le_iff₀ hp]
    linarith

theorem density_noninteger (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6) :
    ¬ ∃ z : ℤ, (z : ℚ) = 2 * density g := by
  rintro ⟨z, hz⟩
  by_cases h5 : g = 5
  · norm_num [density, h5] at hz
    have hz3 : (3 : ℤ) * z = 10 := by
      exact_mod_cast (show (3 : ℚ) * (z : ℚ) = 10 by nlinarith only [hz])
    omega
  · have hg7 : 7 ≤ g := by omega
    have hgQ : (7 : ℚ) ≤ g := by exact_mod_cast hg7
    have hp : (0 : ℚ) < (g : ℚ) - 2 := by linarith
    have hlo : (2 : ℚ) < 2 * density g := by
      rw [density, ← mul_div_assoc, lt_div_iff₀ hp]
      linarith
    have hhi : 2 * density g < (3 : ℚ) := by
      rw [density, ← mul_div_assoc, div_lt_iff₀ hp]
      linarith
    rw [← hz] at hlo hhi
    have hzi : (2 : ℤ) < z := by exact_mod_cast hlo
    have hzj : z < (3 : ℤ) := by exact_mod_cast hhi
    omega

theorem density_cast (g : ℕ) : (density g : ℝ) = (g : ℝ) / ((g : ℝ) - 2) := by
  unfold density
  push_cast
  rfl

theorem coefficient (g : ℕ) (hg : 3 ≤ g) :
    2 * (density g : ℝ) + 1 = 3 + 4 / ((g : ℝ) - 2) := by
  have hgr : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have hp : (0 : ℝ) < (g : ℝ) - 2 := by linarith
  rw [density_cast]
  field_simp [ne_of_gt hp] <;> ring

set_option maxHeartbeats 1500000 in
theorem parameters (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar →
        (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
          dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤
            (3 + 4 / ((g : ℝ) - 2)) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  have hg3 : 3 ≤ g := by omega
  obtain ⟨p, hp⟩ := SeparateDensities.exact_separate_densities (density g) 3
    (density_bounds g hg3).1 (density_bounds g hg3).2 (density_noninteger g hg hne)
  refine ⟨p, ?_⟩
  intro V _ _ G _ hplanar hgirth ports b C
  have hminor := PlanarDensity.minor_density G hplanar
  have hsub := CurrentPlanarFaceBound.induced_density hplanar g hg3 hgirth
  rw [← density_cast] at hsub
  have hh := hp G hminor hsub ports C
  rw [coefficient g hg3] at hh
  exact hh

end Paper.NoncriticalGirth

#print axioms Paper.NoncriticalGirth.density_bounds
#print axioms Paper.NoncriticalGirth.density_noninteger
#print axioms Paper.NoncriticalGirth.density_cast
#print axioms Paper.NoncriticalGirth.coefficient
#print axioms Paper.NoncriticalGirth.parameters
