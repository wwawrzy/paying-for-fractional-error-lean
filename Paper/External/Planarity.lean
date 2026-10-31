import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.Surfaces.OrdinarySurface
/-! External classical planarity input.
Kuratowski (1930), Theorem A, p.278, DOI 10.4064/fm-15-1-271-283;
Wagner (1937), p.570, attributes this characterization to Kuratowski.
This is the sufficient forbidden-minor-to-plane-embedding direction,
with sphere/CW transport and selected-cellulation genus semantics.
These geometric steps are assumed, not proved in Lean here. -/
namespace Paper.External.Planarity
axiom planar_euler_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsPlanar) :
    SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G 0
end Paper.External.Planarity
