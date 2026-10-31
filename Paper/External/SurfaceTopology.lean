import GraphTheory.Topology.ClosedSurface
import GraphTheory.Topology.GraphRealization
import GraphTheory.Surfaces.SignedRotation
/-! External surface-topology assumptions.
A: finite surface triangulation and conversion to mathlib's CW structure.
B: finite-CW Euler characteristic invariance (Hatcher, Theorem 2.44).
C: regular neighborhoods of finite embedded graphs, component capping,
and correspondence with this signed flag rotation encoding.
C combines standard geometric results with the project's representation;
it is not a verbatim single-source theorem. These inputs are axioms. -/
namespace Paper.External.SurfaceTopology
open SimpleGraph OrdinarySurface
axiom exists_cellulation {S : Type} [TopologicalSpace S] (s : ClosedSurface S) :
    Nonempty (Cellulation S)
axiom cellulation_euler_eq {S : Type} [TopologicalSpace S] (s : ClosedSurface S)
    (c d : Cellulation S) : c.eulerCharacteristic = d.eulerCharacteristic
axiom rotation_of_embedding {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Type} [TopologicalSpace S]
    (s : ClosedSurface S) (c : Cellulation S) (h : TopologicalRealization.EmbedsInto G S) :
    ∃ r : SignedRotation G, r.eulerGenus ≤ 2-c.eulerCharacteristic
end Paper.External.SurfaceTopology

