import Paper.Endpoints.Girth.HighGirthFiniteGapSpan
import Mathlib.Order.Interval.Finset.Nat

/-! The actual interval from the first to last attachment, and its original
vertex image. No size bound is built into this trimming definition. -/
namespace Paper.HighGirthTrimmedPath
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
variable (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)

noncomputable def indices {a b : K} (p : K.toSimpleGraph.Walk a b)
    (hS : (HighGirthAttachmentPositions.positions G x K p).Nonempty) : Finset Nat :=
  Finset.Icc ((HighGirthAttachmentPositions.positions G x K p).min' hS)
    ((HighGirthAttachmentPositions.positions G x K p).max' hS)

noncomputable def vertices {a b : K} (p : K.toSimpleGraph.Walk a b)
    (hS : (HighGirthAttachmentPositions.positions G x K p).Nonempty) : Finset V := by
  classical
  exact (indices G x K p hS).image (fun i => (p.getVert i).val.val)

end Paper.HighGirthTrimmedPath

#print axioms Paper.HighGirthTrimmedPath.indices
#print axioms Paper.HighGirthTrimmedPath.vertices
