import GraphTheory.Surfaces.SignedRotationMinorGenus
import Paper.Endpoints.Rounding.SurfaceCount
namespace Paper.SurfaceRounding
variable {V : Type} [Fintype V] [DecidableEq V]
theorem minorBound_of_signedRotation (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SimpleGraph.SignedRotation G) (e : ℝ) (hg : (r.eulerGenus : ℝ) ≤ e) : MinorBound G e := by
  intro W _ _ J _ hm
  exact SimpleGraph.SignedRotation.minor_edge_bound G r J hm e hg
end Paper.SurfaceRounding
