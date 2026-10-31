import Paper.Endpoints.Girth.HighGirthPathFamily
import Paper.Optimality.Treewidth.TreewidthDensity

/-! Genuine path witnesses belong to every minor-density class C_rho
with rho >= 1, independently of the chosen finite girth threshold. -/
namespace Paper.HighGirthMinorPaths
open PathPowerTreewidth

theorem density (n : Nat) (rho : Real) (hrho : 1 ≤ rho) :
    MinorDensity.Bound (graph n 1) rho := by
  have h : MinorDensity.Bound (graph n 1) (1 : Real) :=
    by simpa using TreewidthDensity.minor_density (graph n 1) 1 (PathPowerTreewidth.treeWidth_le n 1)
  intro W _ _ J _ hm
  exact (h W J hm).trans (mul_le_mul_of_nonneg_right hrho (Nat.cast_nonneg _))

end Paper.HighGirthMinorPaths
#print axioms Paper.HighGirthMinorPaths.density
