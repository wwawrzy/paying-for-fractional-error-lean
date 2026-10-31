import Paper.Endpoints.Rounding.SurfaceCount
namespace Paper.SurfaceRounding
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem solver_density (e : ℝ) (he : 0 ≤ e) (hden : MinorBound G e) :
    MinorDensity.Bound G (3 + 3 * e) := by
  intro A _ _ J _ hm
  by_cases hA : Fintype.card A = 0
  · letI : IsEmpty A := Fintype.card_eq_zero_iff.mp hA
    simp
    ext u v
    exact isEmptyElim u
  · have hc : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hA)
    have h := hden A J hm
    nlinarith
end Paper.SurfaceRounding
