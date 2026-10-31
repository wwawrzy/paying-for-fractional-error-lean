import Paper.Endpoints.Rounding.SurfaceRotationMinorBound
import Paper.Endpoints.Rounding.SurfaceSolverDensity
namespace Paper.SurfaceRounding
variable {V : Type} [Fintype V] [DecidableEq V]
theorem minorDensity_of_signedRotation (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SimpleGraph.SignedRotation G) (e : ℝ) (he : 0 ≤ e)
    (hg : (r.eulerGenus : ℝ) ≤ e) : MinorDensity.Bound G (3+3*e) :=
  solver_density G e he (minorBound_of_signedRotation G r e hg)
end Paper.SurfaceRounding
