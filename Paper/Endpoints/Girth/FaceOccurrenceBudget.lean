import GraphTheory.Faces.FacialSeparation

/-!
# Global budget for marked face-edge occurrences

For each marked graph edge, the mod-two boundary support of a face can contain
it only when one of the edge's two oriented darts belongs to that face.  Thus
an edge contributes to at most two actual face indices.  The main theorem
below double-counts these incidences over `FaceIndex`, rather than over dart
representatives (which would count a face more than once).
-/

namespace Paper.GirthFaceOccurrenceBudget

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra

variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Edges incident with a fixed vertex, represented in the graph's edge
finset. -/
noncomputable def incidentEdges (v : V) : Finset G.edgeFinset := by
  classical
  exact Finset.univ.filter fun e => v ∈ (e.1 : Sym2 V)

/-- All edges incident with at least one vertex in `A`. -/
noncomputable def markedEdges (A : Finset V) : Finset G.edgeFinset := by
  classical
  exact A.biUnion incidentEdges

/-- The face-boundary-support edges that touch the marked set. -/
noncomputable def faceMarkedEdges (M : ConnectedPlaneMap G) (A : Finset V)
    (F : FaceIndex M.rawRotation) : Finset G.edgeFinset := by
  classical
  exact (markedEdges A).filter fun e =>
    e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F

/-- The actual faces whose mod-two boundary support contains an edge. -/
noncomputable def supportingFaces (M : ConnectedPlaneMap G)
    (e : G.edgeFinset) : Finset (FaceIndex M.rawRotation) := by
  classical
  exact Finset.univ.filter fun F =>
    e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F

theorem mem_incidentEdges_iff (v : V) (e : G.edgeFinset) :
    e ∈ incidentEdges v ↔ v ∈ (e.1 : Sym2 V) := by
  simp [incidentEdges]

theorem mem_markedEdges_iff (A : Finset V) (e : G.edgeFinset) :
    e ∈ markedEdges A ↔ ∃ v, v ∈ A ∧ v ∈ (e.1 : Sym2 V) := by
  classical
  simp [markedEdges, Finset.mem_biUnion, mem_incidentEdges_iff]

theorem incidentEdges_card_eq_degree (v : V) :
    (incidentEdges (G := G) v).card = G.degree v := by
  classical
  let emb : G.edgeFinset ↪ Sym2 V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (incidentEdges (G := G) v).map emb = G.incidenceFinset v := by
    ext e
    simp [incidentEdges, emb, G.incidenceFinset_eq_filter, and_comm]
  calc
    (incidentEdges (G := G) v).card =
        ((incidentEdges (G := G) v).map emb).card := by simp
    _ = (G.incidenceFinset v).card := by rw [hmap]
    _ = G.degree v := G.card_incidenceFinset_eq_degree v

/-- Counting marked edges by their marked endpoints never exceeds the sum of
the degrees in the marked set.  Edges with both endpoints marked are allowed
to be counted twice on the right. -/
theorem markedEdges_card_le_degree_sum (A : Finset V) :
    (markedEdges (G := G) A).card ≤ ∑ v ∈ A, G.degree v := by
  classical
  calc
    (markedEdges (G := G) A).card ≤ ∑ v ∈ A, (incidentEdges (G := G) v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ A, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact incidentEdges_card_eq_degree v

/-- A supported edge can be incident to at most two actual face indices: the
faces of its two darts. -/
theorem supportingFaces_card_le_two (M : ConnectedPlaneMap G)
    (e : G.edgeFinset) : (supportingFaces M e).card ≤ 2 := by
  classical
  let F₁ := faceIndex M.rawRotation (PlaneTopology.Faces.FaceBoundaryAlgebra.dartOfEdge e)
  let F₂ := faceIndex M.rawRotation (PlaneTopology.Faces.FaceBoundaryAlgebra.dartOfEdge e).symm
  have hsubset : supportingFaces M e ⊆ insert F₁ ({F₂} : Finset _) := by
    intro F hF
    change F ∈ Finset.univ.filter (fun H =>
      e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M H) at hF
    have hsupport :
        e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F :=
      (Finset.mem_filter.mp hF).2
    rcases PlaneTopology.Faces.FacialSeparation.faceBoundarySupport_side M F hsupport with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by simpa [F₁] using h.symm))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (by simpa [F₂] using h.symm)))
  calc
    (supportingFaces M e).card ≤ (insert F₁ ({F₂} : Finset _)).card :=
      Finset.card_le_card hsubset
    _ ≤ ({F₂} : Finset _).card + 1 := Finset.card_insert_le F₁ ({F₂} : Finset _)
    _ = 2 := by simp

/-- Double counting over all face-cycle indices gives the global occurrence
budget: every marked edge is charged at most once for each of its two dart
sides. -/
theorem markedFaceEdges_global_budget (M : ConnectedPlaneMap G)
    (A : Finset V) :
    (∑ F : FaceIndex M.rawRotation, (faceMarkedEdges M A F).card) ≤
      2 * (markedEdges (G := G) A).card := by
  classical
  have hdouble :
      (∑ F : FaceIndex M.rawRotation, (faceMarkedEdges M A F).card) =
        ∑ e ∈ markedEdges (G := G) A, (supportingFaces M e).card := by
    calc
      (∑ F : FaceIndex M.rawRotation, (faceMarkedEdges M A F).card) =
          ∑ F : FaceIndex M.rawRotation,
            ∑ e ∈ markedEdges (G := G) A,
              if e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro F hF
        simp [faceMarkedEdges, Finset.card_filter]
      _ = ∑ e ∈ markedEdges (G := G) A,
            ∑ F : FaceIndex M.rawRotation,
              if e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ e ∈ markedEdges (G := G) A, (supportingFaces M e).card := by
        apply Finset.sum_congr rfl
        intro e he
        symm
        change (Finset.univ.filter (fun F =>
          e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F)).card =
            ∑ F : FaceIndex M.rawRotation,
              if e ∈ PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M F then 1 else 0
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hdouble]
  calc
    (∑ e ∈ markedEdges (G := G) A, (supportingFaces M e).card) ≤
        ∑ e ∈ markedEdges (G := G) A, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact supportingFaces_card_le_two M e
    _ = 2 * (markedEdges (G := G) A).card := by simp [mul_comm]

/-- Consequently the same face-occurrence budget is at most twice the total
marked degree. -/
theorem markedFaceEdges_global_degree_budget (M : ConnectedPlaneMap G)
    (A : Finset V) :
    (∑ F : FaceIndex M.rawRotation, (faceMarkedEdges M A F).card) ≤
      2 * (∑ v ∈ A, G.degree v) := by
  calc
    _ ≤ 2 * (markedEdges (G := G) A).card := markedFaceEdges_global_budget M A
    _ ≤ 2 * (∑ v ∈ A, G.degree v) := by
      exact Nat.mul_le_mul_left 2 (markedEdges_card_le_degree_sum A)

end Paper.GirthFaceOccurrenceBudget
