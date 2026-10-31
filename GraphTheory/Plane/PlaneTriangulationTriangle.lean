import GraphTheory.Plane.PlaneTriangulationPotential
import GraphTheory.Plane.PlaneTriangulationMaximal

/-!
# Triangle edge vectors and actual face potentials

This file supplies the graph-level bridge for the consecutive-toggle
calculation: the characteristic vector of an actual three-cycle is a face
boundary in a supplied sphere map, with explicitly verified incident edges.
-/

namespace PlaneTopology.PlaneTriangulationTriangle

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.Faces.FaceBoundaryAlgebra PlaneTopology.Faces.FacialSeparation PlaneTopology.PlaneTriangulationPotential

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The actual closed walk a-b-c-a. -/
def triangleWalk {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : G.Walk a a :=
  .cons hab (.cons hbc (.cons hca .nil))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Three actual triangle edges form a simple cycle. -/
theorem triangleWalk_isCycle {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : (triangleWalk hab hbc hca).IsCycle := by
  rw [triangleWalk, Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.isPath_def]
    simp [hab.ne', hbc.ne, hca.ne]
  · simp [hab.ne, hab.ne', hbc.ne, hca.ne']

/-- The edge vector of the actual triangle a-b-c-a. -/
def triangleVector {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : EdgeSpace G :=
  (triangleWalk hab hbc hca).edgeVector

/-- The triangle vector belongs to the actual cycle space. -/
theorem triangleVector_mem_cycleSpace {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) :
    triangleVector hab hbc hca ∈ G.CycleSpace :=
  Walk.edgeVector_mem_cycleSpace G (triangleWalk_isCycle hab hbc hca)

/-- Exact coefficient of a dart edge in the triangle vector. -/
theorem triangleVector_apply {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) (d : G.Dart) :
    triangleVector hab hbc hca ⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ =
      if d.edge = s(a, b) ∨ d.edge = s(b, c) ∨ d.edge = s(c, a) then 1 else 0 := by
  simp [triangleVector, Walk.edgeVector, edgeIndicator, Walk.edgeFinset,
    triangleWalk]

/-- At the middle vertex, exactly the two triangle darts have coefficient one. -/
theorem triangleVector_apply_at_middle {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) (d : G.Dart) (hd : d.fst = b) :
    triangleVector hab hbc hca ⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ =
      if d.snd = a ∨ d.snd = c then 1 else 0 := by
  rw [triangleVector_apply]
  simp only [Dart.edge, hd, Sym2.eq_iff, hab.ne', hbc.ne,
    false_and, false_or, or_false, true_and]

/-- At a vertex outside the triangle, every incident coefficient is zero. -/
theorem triangleVector_apply_of_source_away {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) (d : G.Dart)
    (hda : d.fst ≠ a) (hdb : d.fst ≠ b) (hdc : d.fst ≠ c) :
    triangleVector hab hbc hca ⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ = 0 := by
  rw [triangleVector_apply]
  simp only [Dart.edge, Sym2.eq_iff, hda, hdb, hdc, false_and, false_or, if_false]

/-- Every actual triangle vector has a genuine face-boundary potential. -/
theorem exists_triangle_face_potential (M : ConnectedPlaneMap G)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∃ A : FaceChain M.rawRotation,
      faceBoundary M.rawRotation A = triangleVector hab hbc hca := by
  have h := triangleVector_mem_cycleSpace hab hbc hca
  rw [← range_faceBoundary_eq_cycleSpace M] at h
  exact h

/-- Restricting the face-boundary derivative to one outgoing fiber gives
the binary derivative along its actual vertex rotation. -/
theorem facePotential_derivative (M : ConnectedPlaneMap G)
    (A : FaceChain M.rawRotation) (v : V) (d : ↥(outDartsAt G v)) :
    A (faceIndex M.rawRotation d.1) +
        A (faceIndex M.rawRotation ((sigmaOutDartEquiv M.rawRotation v) d).1) =
      faceBoundary M.rawRotation A ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ := by
  rw [faceBoundary_eq_dart_sum]
  congr 1
  exact congrArg A (faceIndex_sigma_eq_symm M.rawRotation d.1)

/-- Any two outgoing darts at a vertex lie in one local rotation orbit. -/
theorem sigmaOutDart_sameCycle (M : ConnectedPlaneMap G) (v : V)
    (d e : ↥(outDartsAt G v)) :
    Equiv.Perm.SameCycle (sigmaOutDartEquiv M.rawRotation v) d e := by
  let σ' : Equiv.Perm ↥(outDartsAt G v) :=
    M.rawRotation.σ.subtypePerm
      (fun _ ↦ (M.rotation.vertexCyclic v).apply_mem_iff)
  have heq : sigmaOutDartEquiv M.rawRotation v = σ' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [heq]
  exact (M.rotation.vertexCyclic v).subtypePerm.2 (Set.mem_univ d) (Set.mem_univ e)

/-- If the boundary vector vanishes on all edges at a vertex, every corner
at that vertex has the same face potential. -/
theorem facePotential_eq_of_incident_zero (M : ConnectedPlaneMap G)
    (A : FaceChain M.rawRotation) (v : V)
    (hzero : ∀ d : ↥(outDartsAt G v),
      faceBoundary M.rawRotation A ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ = 0)
    (d e : ↥(outDartsAt G v)) :
    A (faceIndex M.rawRotation d.1) = A (faceIndex M.rawRotation e.1) := by
  apply eq_of_sameCycle_of_step_eq (sigmaOutDartEquiv M.rawRotation v)
    (fun x ↦ A (faceIndex M.rawRotation x.1)) ?_ (sigmaOutDart_sameCycle M v d e)
  intro x
  have h := (facePotential_derivative M A v x).trans (hzero x)
  have hn := eq_neg_of_add_eq_zero_left h
  simpa only [ZMod.neg_eq_self_mod_two] using hn.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Outgoing darts at a fixed vertex are determined by their targets. -/
theorem outDart_eq_iff_snd_eq {v : V} (d e : ↥(outDartsAt G v)) :
    d = e ↔ d.1.snd = e.1.snd := by
  constructor
  · intro h
    exact congrArg (fun x : ↥(outDartsAt G v) ↦ x.1.snd) h
  · intro h
    apply Subtype.ext
    exact Dart.ext d.1 e.1 (Prod.ext (d.2.trans e.2.symm) h)

/-- A face potential with precisely two consecutive incident triangle edges
is constant outside the corner between those two edges. -/
theorem facePotential_eq_of_consecutive_incident (M : ConnectedPlaneMap G)
    (A : FaceChain M.rawRotation) (v : V) (e f : ↥(outDartsAt G v))
    (hef : e ≠ f) (hsigma : sigmaOutDartEquiv M.rawRotation v e = f)
    (hboundary : ∀ x : ↥(outDartsAt G v),
      faceBoundary M.rawRotation A ⟨x.1.edge, G.mem_edgeFinset.mpr x.1.edge_mem⟩ =
        if x = e ∨ x = f then 1 else 0)
    (d : ↥(outDartsAt G v)) (hdf : d ≠ f) :
    A (faceIndex M.rawRotation d.1) = A (faceIndex M.rawRotation e.1) := by
  apply eq_outside_consecutive_toggles (sigmaOutDartEquiv M.rawRotation v)
    (fun x ↦ A (faceIndex M.rawRotation x.1)) e f hef hsigma ?_
    (sigmaOutDart_sameCycle M v e d) hdf
  intro x
  exact (facePotential_derivative M A v x).trans (hboundary x)

#print axioms exists_triangle_face_potential
#print axioms facePotential_eq_of_incident_zero

end PlaneTopology.PlaneTriangulationTriangle
