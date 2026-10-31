import Paper.Endpoints.Components.SurfaceIncidenceDensity
import Paper.Endpoints.Rounding.SurfaceCount
namespace Paper.SurfacePublicParameters
noncomputable def density (e : ℝ) : ℕ := Nat.ceil (3 + 3 * e)
noncomputable def budget (e : ℝ) : ℕ := max 1 (Nat.ceil (1176 * e))
theorem density_pos (e : ℝ) (he : 0 ≤ e) : 1 ≤ density e := by
  apply Nat.one_le_ceil_iff.mpr
  linarith
theorem budget_pos (e : ℝ) : 1 ≤ budget e := le_max_left _ _
theorem budget_large (e : ℝ) : 1176 * e ≤ (budget e : ℝ) := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (1176 * e))))
theorem incidence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (e : ℝ)
    (he : 0 ≤ e) (hden : SurfaceRounding.MinorBound G e) :
    Incidence.InducedDensityBound
      (CoveringIncidence.graph (SurfaceResidual.cover G d) (CurrentBudget.demands G d)) (density e : ℝ) := by
  apply ComponentDensity.density_mono _ (Nat.le_ceil (3 + 3 * e))
  exact SurfaceResidual.incidence_density G d e he (SurfaceRounding.induced_density G e hden)
end Paper.SurfacePublicParameters
