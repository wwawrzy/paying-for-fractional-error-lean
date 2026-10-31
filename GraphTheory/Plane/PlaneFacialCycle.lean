import GraphTheory.Faces.FacialSeparation

/-!
# Entire facial boundaries are simple cycles in two-connected plane maps

The older HasCyclicFaces interface only extracts a short cycle. Here the
actual whole boundary walk is proved cyclic, retaining every facial vertex.
-/

namespace PlaneTopology.PlaneFacialCycle

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FacialSeparation
  PlaneTopology.Faces.FacialOccurrence.ComponentMap

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph used by the facial-occurrence API stays connected after one
vertex is deleted from a two-connected graph. -/
theorem connected_induceAway (htwo : G.IsKConnected 2) (v : V) :
    (induceAway G v).Connected := by
  letI : Nontrivial V := htwo.two_nontrivial
  have h := htwo.no_cut_vertex G v
  have hset : ((Finset.univ \ {v} : Finset V) : Set V) = {w | w ≠ v} := by
    ext w
    simp
  rw [hset] at h
  exact h

/-- Two occurrences of one source on the same actual face coincide. -/
theorem eq_of_sameFace_of_source_eq (M : ConnectedPlaneMap G)
    (htwo : G.IsKConnected 2) (d e : G.Dart)
    (hface : M.rawRotation.SameFace d e) (hsource : d.fst = e.fst) : d = e := by
  by_contra hne
  let d' : ↥(outDartsAt G d.fst) := ⟨d, rfl⟩
  let e' : ↥(outDartsAt G d.fst) := ⟨e, hsource.symm⟩
  have hne' : d' ≠ e' := fun h => hne (congrArg Subtype.val h)
  have hreach := (connected_induceAway htwo d.fst).preconnected
    (outDartTargetAway d.fst d') (outDartTargetAway d.fst e')
  obtain ⟨z, hz, hincident⟩ :=
    exists_cycleSpace_two_incident_of_reachable_away d.fst d' e' hne' hreach
  exact not_sameFace_of_cycleSpace_two_incident M d.fst d' e' hne' z hz hincident hface

/-- The target map on an actual two-connected facial orbit is injective too. -/
theorem eq_of_sameFace_of_target_eq (M : ConnectedPlaneMap G)
    (htwo : G.IsKConnected 2) (d e : G.Dart)
    (hface : M.rawRotation.SameFace d e) (htarget : d.snd = e.snd) : d = e := by
  apply M.rawRotation.facePerm.injective
  apply eq_of_sameFace_of_source_eq M htwo
  · exact Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.apply_left hface)
  · simpa only [RotationSystem.facePerm_source] using htarget

/-- The whole actual facial boundary is a simple graph cycle, not merely a
walk from which some shorter cycle can be extracted. -/
theorem faceBoundaryWalk_isCycle (M : ConnectedPlaneMap G)
    (htwo : G.IsKConnected 2) (base : G.Dart) :
    (M.rawRotation.faceBoundaryWalk base).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨faceBoundaryWalk_isTrail_of_isKConnected_two M htwo base, ?_, ?_⟩
  · intro hnil
    have hlength := M.rawRotation.faceBoundaryWalk_length base
    rw [hnil] at hlength
    have hpos := M.rawRotation.faceDegree_pos base
    simp only [Walk.length_nil] at hlength
    omega
  · rw [← Walk.map_snd_darts, M.rawRotation.faceBoundaryWalk_darts]
    apply List.Nodup.map_on
    · intro d hd e he htarget
      have hdface : M.rawRotation.SameFace base d :=
        (Equiv.Perm.mem_toList_iff.mp hd).1
      have heface : M.rawRotation.SameFace base e :=
        (Equiv.Perm.mem_toList_iff.mp he).1
      exact eq_of_sameFace_of_target_eq M htwo d e (hdface.symm.trans heface) htarget
    · exact Equiv.Perm.nodup_toList M.rawRotation.facePerm base

/-- Every actual cofacial source lies on the whole simple facial cycle. -/
theorem source_mem_faceBoundaryWalk_of_sameFace (M : ConnectedPlaneMap G)
    (base d : G.Dart) (hface : M.rawRotation.SameFace base d) :
    d.fst ∈ (M.rawRotation.faceBoundaryWalk base).support := by
  apply Walk.dart_fst_mem_support_of_mem_darts
  rw [M.rawRotation.faceBoundaryWalk_darts]
  exact Equiv.Perm.mem_toList_iff.mpr
    ⟨hface, Equiv.Perm.mem_support.mpr (M.rawRotation.facePerm_ne_self base)⟩

#print axioms eq_of_sameFace_of_source_eq
#print axioms faceBoundaryWalk_isCycle
#print axioms source_mem_faceBoundaryWalk_of_sameFace

end PlaneTopology.PlaneFacialCycle
