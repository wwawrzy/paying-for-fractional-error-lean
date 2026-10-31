import GraphTheory.Plane.PlaneTriangulationTriangle

/-!
# A triangle corner cannot connect across its own face

This is an algebraic sphere-map separation theorem. A triangle using two
consecutive edges at b isolates that face corner. A fourth cofacial vertex
cannot also be adjacent to b, because the triangle face potential would then
be simultaneously equal and unequal across the extra edge.
-/

namespace PlaneTopology.PlaneTriangulationCrossing

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.Faces.FaceBoundaryAlgebra PlaneTopology.Faces.FacialSeparation PlaneTopology.PlaneTriangulationTriangle

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No edge from a triangle corner to a fourth vertex on that same face.
All edges, darts, face membership and rotation relations are actual map data. -/
theorem no_fourth_neighbor_at_triangle_corner (M : ConnectedPlaneMap G)
    {a b c w : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hbw : G.Adj b w) (hwa : w ≠ a) (hwc : w ≠ c)
    (hcorner : M.rawRotation.σ (⟨(b, a), hab.symm⟩ : G.Dart) =
      (⟨(b, c), hbc⟩ : G.Dart))
    (dw : G.Dart) (hdw : dw.fst = w)
    (hface : M.rawRotation.SameFace (⟨(b, c), hbc⟩ : G.Dart) dw) : False := by
  classical
  obtain ⟨A, hA⟩ := exists_triangle_face_potential M hab hbc hca
  let e : ↥(outDartsAt G b) := ⟨⟨(b, a), hab.symm⟩, rfl⟩
  let f : ↥(outDartsAt G b) := ⟨⟨(b, c), hbc⟩, rfl⟩
  let t : ↥(outDartsAt G b) := ⟨⟨(b, w), hbw⟩, rfl⟩
  have hef : e ≠ f := by
    intro h
    exact hca.ne ((outDart_eq_iff_snd_eq e f).mp h).symm
  have htf : t ≠ f := by
    intro h
    exact hwc ((outDart_eq_iff_snd_eq t f).mp h)
  have hsigma : sigmaOutDartEquiv M.rawRotation b e = f := by
    apply Subtype.ext
    exact hcorner
  have hboundary : ∀ x : ↥(outDartsAt G b),
      faceBoundary M.rawRotation A ⟨x.1.edge, G.mem_edgeFinset.mpr x.1.edge_mem⟩ =
        if x = e ∨ x = f then 1 else 0 := by
    intro x
    rw [hA, triangleVector_apply_at_middle hab hbc hca x.1 x.2]
    simp only [outDart_eq_iff_snd_eq]
    rfl
  have hte : A (faceIndex M.rawRotation t.1) = A (faceIndex M.rawRotation e.1) :=
    facePotential_eq_of_consecutive_incident M A b e f hef hsigma hboundary t htf
  let tw : ↥(outDartsAt G w) := ⟨t.1.symm, rfl⟩
  let dw' : ↥(outDartsAt G w) := ⟨dw, hdw⟩
  have hwzero : ∀ x : ↥(outDartsAt G w),
      faceBoundary M.rawRotation A ⟨x.1.edge, G.mem_edgeFinset.mpr x.1.edge_mem⟩ = 0 := by
    intro x
    rw [hA]
    apply triangleVector_apply_of_source_away hab hbc hca x.1
    · exact fun h ↦ hwa (x.2.symm.trans h)
    · exact fun h ↦ hbw.ne (x.2.symm.trans h).symm
    · exact fun h ↦ hwc (x.2.symm.trans h)
  have htw : A (faceIndex M.rawRotation t.1.symm) = A (faceIndex M.rawRotation dw) :=
    facePotential_eq_of_incident_zero M A w hwzero tw dw'
  have htdzero : faceBoundary M.rawRotation A
      ⟨t.1.edge, G.mem_edgeFinset.mpr t.1.edge_mem⟩ = 0 := by
    rw [hA, triangleVector_apply_at_middle hab hbc hca t.1 t.2]
    simp only [t, hwa, hwc, false_or, if_false]
  have htd : A (faceIndex M.rawRotation t.1) = A (faceIndex M.rawRotation t.1.symm) := by
    have hsum := (faceBoundary_eq_dart_sum M.rawRotation A t.1).symm.trans htdzero
    have hneg := eq_neg_of_add_eq_zero_left hsum
    simpa only [ZMod.neg_eq_self_mod_two] using hneg
  have hdf : A (faceIndex M.rawRotation dw) = A (faceIndex M.rawRotation f.1) := by
    exact congrArg A ((faceIndex_eq_iff_sameFace M.rawRotation _ _).mpr hface).symm
  have hefA : A (faceIndex M.rawRotation e.1) = A (faceIndex M.rawRotation f.1) :=
    hte.symm.trans (htd.trans (htw.trans hdf))
  have hone := (facePotential_derivative M A b e).trans (hboundary e)
  rw [hsigma] at hone
  simp only [true_or, if_true] at hone
  rw [hefA, ZModModule.add_self] at hone
  exact zero_ne_one hone

#print axioms no_fourth_neighbor_at_triangle_corner

end PlaneTopology.PlaneTriangulationCrossing
