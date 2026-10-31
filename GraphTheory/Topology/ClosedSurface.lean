import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Geometry.Manifold.ChartedSpace
/-! Actual compact connected closed topological surfaces and finite CW cellulations.
No rotation or density premise occurs in these structures. -/
namespace SimpleGraph.OrdinarySurface
structure ClosedSurface (S : Type) [TopologicalSpace S] where
  hausdorff : T2Space S
  compact : CompactSpace S
  connected : ConnectedSpace S
  secondCountable : SecondCountableTopology S
  charts : ChartedSpace (Fin 2 → ℝ) S
structure Cellulation (S : Type) [TopologicalSpace S] where
  cw : Topology.CWComplex (Set.univ : Set S)
  finite_cells : ∀ n, Finite (cw.cell n)
  no_high_cells : ∀ n, 3 ≤ n → IsEmpty (cw.cell n)
noncomputable def Cellulation.eulerCharacteristic {S : Type} [TopologicalSpace S]
    (c : Cellulation S) : ℤ :=
  (Nat.card (c.cw.cell 0) : ℤ) - (Nat.card (c.cw.cell 1) : ℤ) + (Nat.card (c.cw.cell 2) : ℤ)
end SimpleGraph.OrdinarySurface

