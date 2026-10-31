import GraphTheory.Plane.PlaneVertexDeletionLeaf
import GraphTheory.Plane.PlaneFanInsertion
import Mathlib.Logic.Equiv.Option

/-! # Actual vertex deletion exposing all former neighbours on one face -/

namespace PlaneTopology.PlaneVertexDeletion

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneChordFaces PlaneTopology.PlaneFanInsertion PlaneTopology.PlaneEdgeInsertion
open PlaneTopology.PlaneEdgeDeletion PlaneTopology.PlanePermutationDeletion PlaneTopology.PlaneLeafInsertion

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The endpoints of every actual edge share a face in every rotation. -/
theorem coFacial_of_adj (r : G.RotationSystem) {u v : V} (huv : G.Adj u v) :
    CoFacial G r u v := by
  let d : G.Dart := ⟨(u, v), huv⟩
  exact ⟨d, r.facePerm d, rfl, r.facePerm_source d, ⟨1, by simp⟩⟩

/-- Deleting an edge from a plane map preserves every actual cofacial pair
of vertices, replacing a removed witness by the exposed corner at its source. -/
theorem coFacial_deleted (u v : V) (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (M : ConnectedPlaneMap (G ⊔ edge u v)) (hG : G.Connected) (a b : V)
    (hab : CoFacial (G ⊔ edge u v) M.rawRotation a b) :
    CoFacial G (deleteInsertedEdgePlaneMap G u v hne hmiss M hG).rawRotation a b := by
  obtain ⟨d, e, hds, hes, hd, he, hde⟩ := exists_deleted_corners G u v hne hmiss M hG
  have hwitness (z : G.Dart ⊕ Bool) : ∃ f : G.Dart,
      f.fst = (augmentedDart G u v hne z).fst ∧
        (deletedRotation G u v hne hmiss M.rawRotation).SameFace (chordCollapse d e z) f := by
    cases z with
    | inl z => exact ⟨z, rfl, SameCycle.refl _ _⟩
    | inr z =>
      cases z
      · exact ⟨d, hds, hde.symm⟩
      · exact ⟨e, hes, hde⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := hab
  obtain ⟨x, rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective x
  obtain ⟨y, rfl⟩ := (augmentedDartEquiv G u v hne hmiss).surjective y
  obtain ⟨x', hx', hfx⟩ := hwitness x
  obtain ⟨y', hy', hfy⟩ := hwitness y
  refine ⟨x', y', hx'.trans hx, hy'.trans hy, ?_⟩
  exact hfx.symm.trans ((deletedRotation_sameFace_of_sameFace G u v hne hmiss M.rawRotation
    d e hds hes hd he hde x y hxy).trans hfy)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A singleton apex graph is exactly a fresh leaf graph. -/
theorem apexGraph_singleton (v : V) : apexGraph G {v} = leafGraph G v := by
  ext a b
  cases a <;> cases b <;> simp [apexGraph, leafGraph, eq_comm]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Expose one apex spoke as a missing-edge augmentation. -/
theorem apexGraph_insert (v : V) (S : Finset V) :
    apexGraph G (insert v S) = apexGraph G S ⊔ edge none (some v) := by
  ext a b
  cases a <;> cases b <;> simp [apexGraph, edge_adj, eq_comm, or_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Any nonempty apex neighbourhood preserves connectedness of the old graph. -/
theorem connected_apexGraph (hG : G.Connected) (S : Finset V) (hS : S.Nonempty) :
    (apexGraph G S).Connected := by
  obtain ⟨v, hv⟩ := hS
  apply (PlaneTopology.PlaneLeafInsertion.connected_leafGraph G v hG).mono
  intro a b hab
  cases a <;> cases b <;> simp_all [leafGraph, apexGraph]

/-- Delete a nonempty apex neighbourhood from any supplied actual plane map.
All vertices formerly cofacial with the apex lie on one common residual face. -/
theorem exists_deleteApexPlaneMap (hG : G.Connected) (hD : Nonempty G.Dart)
    (S : Finset V) (hS : S.Nonempty) (M : ConnectedPlaneMap (apexGraph G S)) :
    ∃ N : ConnectedPlaneMap G, ∃ base : G.Dart, ∀ w : V,
      CoFacial (apexGraph G S) M.rawRotation none (some w) →
      ∃ e : G.Dart, e.fst = w ∧ N.rawRotation.SameFace base e := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert v S hv ih =>
    by_cases hempty : S = ∅
    · subst S
      have heq : apexGraph G (insert v ∅) = leafGraph G v := apexGraph_singleton G v
      let L := castPlaneMap heq M
      obtain ⟨base, hb⟩ := PlaneTopology.PlaneVertexDeletionLeaf.exists_common_face_after_leaf G v L hG hD
      refine ⟨PlaneTopology.PlaneVertexDeletionLeaf.deleteLeafPlaneMap G v L hG hD, base, ?_⟩
      intro w hw
      exact hb w (castPlaneMap_coFacial heq M none (some w) hw)
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have hconn := connected_apexGraph G hG S hSne
      have hne : (none : Option V) ≠ some v := by simp
      have hmiss : ¬ (apexGraph G S).Adj none (some v) := hv
      let L := castPlaneMap (apexGraph_insert G v S) M
      let D := deleteInsertedEdgePlaneMap (apexGraph G S) none (some v) hne hmiss L hconn
      obtain ⟨N, base, hb⟩ := ih hSne D
      refine ⟨N, base, ?_⟩
      intro w hw
      apply hb w
      exact coFacial_deleted (apexGraph G S) none (some v) hne hmiss L hconn none (some w)
        (castPlaneMap_coFacial (apexGraph_insert G v S) M none (some w) hw)

/-- Reinsert the deleted vertex as the explicit apex of its actual residual graph. -/
noncomputable def apexResidualIso (v : V) :
    apexGraph (G.induce {w | w ≠ v})
      (Finset.univ.filter (fun w : {w // w ≠ v} => G.Adj v w)) ≃g G where
  toEquiv := Equiv.optionSubtypeNe v
  map_rel_iff' := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => change G.Adj v v ↔ False; simp
      | some b =>
        change G.Adj v b.val ↔ b ∈ Finset.univ.filter (fun w : {w // w ≠ v} => G.Adj v w)
        exact ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
          fun h => (Finset.mem_filter.mp h).2⟩
    | some a =>
      cases b with
      | none =>
        change G.Adj a.val v ↔ a ∈ Finset.univ.filter (fun w : {w // w ≠ v} => G.Adj v w)
        exact ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩,
          fun h => (Finset.mem_filter.mp h).2.symm⟩
      | some b => change G.Adj a.val b.val ↔ G.Adj a.val b.val; rfl

/-- Actual deletion of a vertex from a connected plane map, whenever its
residual graph is connected and has a dart. All former neighbours share one
genuine face of the constructed residual map. -/
theorem exists_deleteVertexPlaneMap (v : V) (M : ConnectedPlaneMap G)
    (hconn : (G.induce {w | w ≠ v}).Connected)
    (hD : Nonempty (G.induce {w | w ≠ v}).Dart) :
    ∃ N : ConnectedPlaneMap (G.induce {w | w ≠ v}),
      ∃ base : (G.induce {w | w ≠ v}).Dart,
        ∀ w : {w // w ≠ v}, G.Adj v w →
          ∃ e : (G.induce {w | w ≠ v}).Dart,
            e.fst = w ∧ N.rawRotation.SameFace base e := by
  classical
  let H := G.induce {w | w ≠ v}
  let S : Finset {w // w ≠ v} := Finset.univ.filter (fun w => G.Adj v w)
  have hS : S.Nonempty := by
    obtain ⟨d⟩ := hD
    haveI : Nontrivial V := ⟨⟨d.fst.val, d.snd.val, G.ne_of_adj d.adj⟩⟩
    obtain ⟨w, hw⟩ := M.connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨⟨w, (G.ne_of_adj hw).symm⟩, by simpa [S] using hw⟩
  let L : ConnectedPlaneMap (apexGraph H S) :=
    PlaneTopology.PlaneGeneralTransport.planeMap (apexResidualIso G v).symm M
  obtain ⟨N, base, hb⟩ := exists_deleteApexPlaneMap H hconn hD S hS L
  refine ⟨N, base, ?_⟩
  intro w hw
  apply hb w
  apply coFacial_of_adj
  change w ∈ S
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩

end PlaneTopology.PlaneVertexDeletion

#print axioms PlaneTopology.PlaneVertexDeletion.coFacial_deleted
#print axioms PlaneTopology.PlaneVertexDeletion.exists_deleteApexPlaneMap
#print axioms PlaneTopology.PlaneVertexDeletion.exists_deleteVertexPlaneMap
