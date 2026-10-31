import GraphTheory.Plane.PlaneEdgeInsertion
import GraphTheory.Faces.FacialSeparation
import Mathlib.Order.Max

/-!
# Maximal actual plane extensions and their facial rigidity

Maximality below concerns actual connected faithful sphere maps, not the
forbidden-minor predicate. A missing cofacial edge can therefore be inserted
using the proved map operation. Facial separation then excludes repeated
source vertices on a face. No edge saturation equality is assumed.
-/

namespace PlaneTopology.PlaneTriangulationMaximal

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FacialSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Existence of an actual connected faithful sphere map, with the decidable
adjacency instance chosen canonically to make this a predicate on graphs. -/
def HasPlaneMap (G : SimpleGraph V) : Prop := by
  classical
  exact Nonempty (ConnectedPlaneMap G)

/-- Any supplied actual plane map witnesses the map-existence predicate. -/
theorem hasPlaneMap_of_map {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : ConnectedPlaneMap G) : HasPlaneMap G := by
  unfold HasPlaneMap
  have hdec : (fun a b : V ↦ Classical.propDecidable (G.Adj a b)) =
      (inferInstance : DecidableRel G.Adj) := Subsingleton.elim _ _
  rw [hdec]
  exact ⟨M⟩

/-- Finite maximal extension in the class of graphs carrying actual plane
maps, without assuming any numerical saturation statement. -/
theorem exists_maximal_plane_supergraph {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : ConnectedPlaneMap G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ Maximal HasPlaneMap T :=
  Finite.exists_le_maximal (hasPlaneMap_of_map M)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At maximality, every two distinct vertices incident with one face are
adjacent: otherwise the actual chord-insertion construction extends the map. -/
theorem adjacent_of_sameFace_of_maximal (hmax : Maximal HasPlaneMap G)
    (M : ConnectedPlaneMap G) (d e : G.Dart)
    (hne : d.fst ≠ e.fst) (hface : M.rawRotation.SameFace d e) :
    G.Adj d.fst e.fst := by
  by_contra hmiss
  have hnew := hasPlaneMap_of_map
    (PlaneTopology.PlaneEdgeInsertion.insertedPlaneMap G d.fst e.fst M d e hne hmiss rfl rfl hface)
  have hle : G ⊔ edge d.fst e.fst ≤ G := hmax.2 hnew le_sup_left
  exact (G.lt_sup_edge d.fst e.fst hne hmiss).not_ge hle

/-- Two different occurrences of one vertex cannot lie on one maximal-map
face: their distinct targets would be adjacent on that same face and hence
connected after deleting the repeated vertex, contradicting facial separation. -/
theorem eq_of_sameFace_of_source_eq_of_maximal (hmax : Maximal HasPlaneMap G)
    (M : ConnectedPlaneMap G) (d e : G.Dart)
    (hface : M.rawRotation.SameFace d e) (hsource : d.fst = e.fst) : d = e := by
  by_contra hne
  have htarget : d.snd ≠ e.snd := by
    intro h
    exact hne (Dart.ext d e (Prod.ext hsource h))
  have hface' : M.rawRotation.SameFace (M.rawRotation.facePerm d)
      (M.rawRotation.facePerm e) := by
    exact Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.apply_left hface)
  have htargetAdj : G.Adj d.snd e.snd := by
    simpa only [SimpleGraph.RotationSystem.facePerm_source] using
      adjacent_of_sameFace_of_maximal hmax M
        (M.rawRotation.facePerm d) (M.rawRotation.facePerm e)
        (by simpa only [SimpleGraph.RotationSystem.facePerm_source] using htarget) hface'
  let d' : ↥(outDartsAt G d.fst) := ⟨d, rfl⟩
  let e' : ↥(outDartsAt G d.fst) := ⟨e, hsource.symm⟩
  have hne' : d' ≠ e' := by
    intro h
    exact hne (congrArg Subtype.val h)
  have hreach : (PlaneTopology.Faces.FacialOccurrence.ComponentMap.induceAway G d.fst).Reachable
      (outDartTargetAway d.fst d') (outDartTargetAway d.fst e') :=
    Adj.reachable htargetAdj
  obtain ⟨z, hz, hincident⟩ :=
    exists_cycleSpace_two_incident_of_reachable_away d.fst d' e' hne' hreach
  exact not_sameFace_of_cycleSpace_two_incident M d.fst d' e' hne' z hz hincident hface

/-- The source map on the actual darts of each maximal-map face is injective. -/
theorem face_source_injective_of_maximal (hmax : Maximal HasPlaneMap G)
    (M : ConnectedPlaneMap G) (base : G.Dart) :
    Function.Injective (fun d : PlaneTopology.Faces.FacialOccurrence.FaceBoundary.FaceCorner M.rawRotation base ↦
      d.1.fst) := by
  intro d e h
  apply Subtype.ext
  exact eq_of_sameFace_of_source_eq_of_maximal hmax M d.1 e.1
    (M.rawRotation.sameFace_equivalence.trans
      (M.rawRotation.sameFace_equivalence.symm d.2) e.2) h

#print axioms exists_maximal_plane_supergraph
#print axioms adjacent_of_sameFace_of_maximal
#print axioms face_source_injective_of_maximal

end PlaneTopology.PlaneTriangulationMaximal
