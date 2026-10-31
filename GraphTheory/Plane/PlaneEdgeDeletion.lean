import GraphTheory.Plane.PlanePermutationDeletion
import GraphTheory.Plane.PlaneEdgeInsertion
import GraphTheory.Plane.PlaneChordCountBound
import GraphTheory.Plane.PlaneChordCountExact
import GraphTheory.Plane.CellularEuler
import GraphTheory.Plane.PlaneGeneralTransport

/-! # Actual edge deletion from a connected plane map -/

namespace PlaneTopology.PlaneEdgeDeletion

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlanePermutationDeletion PlaneTopology.PlaneEdgeInsertion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- Express the original rotation on old darts plus the two removed darts. -/
noncomputable def pulledPerm (r : (G ⊔ edge u v).RotationSystem) : Perm (G.Dart ⊕ Bool) :=
  (augmentedDartEquiv G u v hne hmiss).symm.permCongr r.σ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The pulled-back rotation still preserves actual sources. -/
theorem pulledPerm_source (r : (G ⊔ edge u v).RotationSystem) (a : G.Dart ⊕ Bool) :
    (augmentedDart G u v hne (pulledPerm G u v hne hmiss r a)).fst =
      (augmentedDart G u v hne a).fst := by
  change ((augmentedDartEquiv G u v hne hmiss)
    (pulledPerm G u v hne hmiss r a)).fst =
      ((augmentedDartEquiv G u v hne hmiss) a).fst
  simp only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact r.σ_source _

/-- Pullback of faithful vertex-cycle membership. -/
theorem pulledPerm_sameCycle (R : FaithfulRotationSystem (G ⊔ edge u v))
    (a b : G.Dart ⊕ Bool)
    (hab : (augmentedDart G u v hne a).fst = (augmentedDart G u v hne b).fst) :
    (pulledPerm G u v hne hmiss R.toRotationSystem).SameCycle a b := by
  have h := R.sameCycle_at_source hab
  have hm := PlaneTopology.PlanePermutationSurgery.sameCycle_map R.toRotationSystem.σ
    (pulledPerm G u v hne hmiss R.toRotationSystem)
    (augmentedDartEquiv G u v hne hmiss).symm
    (fun a => by simp [pulledPerm]) h
  change (pulledPerm G u v hne hmiss R.toRotationSystem).SameCycle
    ((augmentedDartEquiv G u v hne hmiss).symm ((augmentedDartEquiv G u v hne hmiss) a))
    ((augmentedDartEquiv G u v hne hmiss).symm ((augmentedDartEquiv G u v hne hmiss) b)) at hm
  simpa only [Equiv.symm_apply_apply] using hm

/-- Remove the two fresh darts, first the reverse orientation and then the forward one. -/
noncomputable def erasedPerm (r : (G ⊔ edge u v).RotationSystem) : Perm (G.Dart ⊕ Bool) :=
  erasePoint (erasePoint (pulledPerm G u v hne hmiss r) (Sum.inr true)) (Sum.inr false)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Both deleted darts are fixed after bypassing their old vertex positions. -/
theorem erasedPerm_fixed (r : (G ⊔ edge u v).RotationSystem) (b : Bool) :
    erasedPerm G u v hne hmiss r (Sum.inr b) = Sum.inr b := by
  cases b
  · exact erasePoint_fixed _ _
  · rw [erasedPerm, erasePoint_apply_of_ne _ _ _ (by simp)]
    · exact erasePoint_fixed _ _
    · rw [erasePoint_fixed]
      simp

omit [Fintype V] [DecidableRel G.Adj] in
/-- Bypassing the deleted darts continues to preserve actual vertex labels. -/
theorem erasedPerm_source (r : (G ⊔ edge u v).RotationSystem) (a : G.Dart ⊕ Bool) :
    (augmentedDart G u v hne (erasedPerm G u v hne hmiss r a)).fst =
      (augmentedDart G u v hne a).fst := by
  let f := fun z : G.Dart ⊕ Bool => (augmentedDart G u v hne z).fst
  exact erasePoint_preserves _ _ f
    (fun b => erasePoint_preserves _ _ f (pulledPerm_source G u v hne hmiss r) b) a

/-- Surviving darts with a common source remain on one vertex cycle. -/
theorem erasedPerm_sameCycle_old (R : FaithfulRotationSystem (G ⊔ edge u v))
    (a b : G.Dart) (hab : a.fst = b.fst) :
    (erasedPerm G u v hne hmiss R.toRotationSystem).SameCycle (Sum.inl a) (Sum.inl b) := by
  apply erasePoint_sameCycle _ _ (by simp) (by simp)
  apply erasePoint_sameCycle _ _ (by simp) (by simp)
  exact pulledPerm_sameCycle G u v hne hmiss R _ _ hab

/-- The actual source-preserving rotation after deleting the edge. -/
noncomputable def deletedRotation (r : (G ⊔ edge u v).RotationSystem) : G.RotationSystem where
  σ := restrictLeft (erasedPerm G u v hne hmiss r) (erasedPerm_fixed G u v hne hmiss r)
  σ_source a := by
    have h := erasedPerm_source G u v hne hmiss r (Sum.inl a)
    rw [← restrictLeft_inl_apply _ (erasedPerm_fixed G u v hne hmiss r)] at h
    exact h

/-- Exact faithfulness of the restricted actual graph rotation. -/
noncomputable def deletedFaithfulRotation (R : FaithfulRotationSystem (G ⊔ edge u v)) :
    FaithfulRotationSystem G where
  toRotationSystem := deletedRotation G u v hne hmiss R.toRotationSystem
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro w a ha b hb
    exact restrictLeft_sameCycle _ (erasedPerm_fixed G u v hne hmiss R.toRotationSystem)
      (erasedPerm_sameCycle_old G u v hne hmiss R a b (ha.trans hb.symm))

include hne in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex in the connected remaining graph has an outgoing dart. -/
theorem exists_dart_of_connected (hG : G.Connected) (w : V) :
    ∃ d : G.Dart, d.fst = w := by
  haveI : Nontrivial V := ⟨⟨u, v, hne⟩⟩
  obtain ⟨z, hwz⟩ := hG.preconnected.exists_adj_of_nontrivial w
  exact ⟨⟨(w, z), hwz⟩, rfl⟩

/-- The successor of the removed forward dart is a surviving old dart at `u`. -/
theorem exists_forward_successor (R : FaithfulRotationSystem (G ⊔ edge u v))
    (hG : G.Connected) : ∃ d : G.Dart, d.fst = u ∧
      pulledPerm G u v hne hmiss R.toRotationSystem (Sum.inr false) = Sum.inl d := by
  obtain ⟨a, ha⟩ := exists_dart_of_connected G u v hne hG u
  have hc := pulledPerm_sameCycle G u v hne hmiss R (Sum.inr false) (Sum.inl a) ha.symm
  let p := pulledPerm G u v hne hmiss R.toRotationSystem
  have hnf : p (Sum.inr false) ≠ Sum.inr false := by
    intro h
    have heq := hc.eq_of_left h
    cases heq
  have hs := pulledPerm_source G u v hne hmiss R.toRotationSystem (Sum.inr false)
  change (augmentedDart G u v hne (p (Sum.inr false))).fst = u at hs
  cases hp : p (Sum.inr false) with
  | inl d => exact ⟨d, by simpa only [hp] using hs, rfl⟩
  | inr b =>
    cases b
    · exact (hnf hp).elim
    · have hvu : v = u := by simpa only [hp] using hs
      exact (hne hvu.symm).elim

/-- The successor of the removed reverse dart is a surviving old dart at `v`. -/
theorem exists_reverse_successor (R : FaithfulRotationSystem (G ⊔ edge u v))
    (hG : G.Connected) : ∃ e : G.Dart, e.fst = v ∧
      pulledPerm G u v hne hmiss R.toRotationSystem (Sum.inr true) = Sum.inl e := by
  obtain ⟨a, ha⟩ := exists_dart_of_connected G u v hne hG v
  have hc := pulledPerm_sameCycle G u v hne hmiss R (Sum.inr true) (Sum.inl a) ha.symm
  let p := pulledPerm G u v hne hmiss R.toRotationSystem
  have hnf : p (Sum.inr true) ≠ Sum.inr true := by
    intro h
    have heq := hc.eq_of_left h
    cases heq
  have hs := pulledPerm_source G u v hne hmiss R.toRotationSystem (Sum.inr true)
  change (augmentedDart G u v hne (p (Sum.inr true))).fst = v at hs
  cases hp : p (Sum.inr true) with
  | inl e => exact ⟨e, by simpa only [hp] using hs, rfl⟩
  | inr b =>
    cases b
    · have huv : u = v := by simpa only [hp] using hs
      exact (hne huv).elim
    · exact (hnf hp).elim

omit [Fintype V] [DecidableRel G.Adj] in
/-- Exact inverse identity: reinserting the deleted edge recovers the original
vertex permutation, not merely an isomorphic collection of cycles. -/
theorem augmentedRotation_deletedRotation (r : (G ⊔ edge u v).RotationSystem)
    (d e : G.Dart)
    (hd : pulledPerm G u v hne hmiss r (Sum.inr false) = Sum.inl d)
    (he : pulledPerm G u v hne hmiss r (Sum.inr true) = Sum.inl e) :
    augmentedRotation G (deletedRotation G u v hne hmiss r) d e =
      pulledPerm G u v hne hmiss r := by
  let p := pulledPerm G u v hne hmiss r
  have hs : erasePoint p (Sum.inr true) (Sum.inr false) = Sum.inl d := by
    rw [erasePoint_apply_of_ne p _ _ (by simp) (by rw [hd]; simp)]
    exact hd
  have hq := sumCongr_restrictLeft (erasedPerm G u v hne hmiss r)
    (erasedPerm_fixed G u v hne hmiss r)
  change baseRotation G (deletedRotation G u v hne hmiss r) =
    erasePoint (erasePoint p (Sum.inr true)) (Sum.inr false) at hq
  rw [erasePoint, hs, erasePoint, he] at hq
  rw [augmentedRotation, hq]
  rw [Equiv.swap_comm (Sum.inr false) (Sum.inl d),
    Equiv.swap_comm (Sum.inr true) (Sum.inl e)]
  simp [← mul_assoc, p]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A source-preserving rotation is determined by its permutation. -/
theorem rotation_eq_of_sigma_eq {r s : G.RotationSystem} (h : r.σ = s.σ) : r = s := by
  cases r
  cases s
  cases h
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- Exact reconstruction of the original rotation after deleting and reinserting
its edge at the surviving successors. -/
theorem insertedRotation_deletedRotation (r : (G ⊔ edge u v).RotationSystem)
    (d e : G.Dart) (hds : d.fst = u) (hes : e.fst = v)
    (hd : pulledPerm G u v hne hmiss r (Sum.inr false) = Sum.inl d)
    (he : pulledPerm G u v hne hmiss r (Sum.inr true) = Sum.inl e) :
    insertedRotation G u v (deletedRotation G u v hne hmiss r) d e hne hmiss hds hes = r := by
  apply rotation_eq_of_sigma_eq
  apply Equiv.ext
  intro a
  change (augmentedDartEquiv G u v hne hmiss)
    (augmentedRotation G (deletedRotation G u v hne hmiss r) d e
      ((augmentedDartEquiv G u v hne hmiss).symm a)) = r.σ a
  rw [augmentedRotation_deletedRotation G u v hne hmiss r d e hd he]
  simp only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

/-- Exact face-merging interface. Once the surviving cut corners are cofacial,
all original incidences collapse to actual incidences of the deleted rotation. -/
theorem deletedRotation_sameFace_of_sameFace (r : (G ⊔ edge u v).RotationSystem)
    (d e : G.Dart) (hds : d.fst = u) (hes : e.fst = v)
    (hd : pulledPerm G u v hne hmiss r (Sum.inr false) = Sum.inl d)
    (he : pulledPerm G u v hne hmiss r (Sum.inr true) = Sum.inl e)
    (hde : (deletedRotation G u v hne hmiss r).SameFace d e)
    (x y : G.Dart ⊕ Bool)
    (hxy : r.SameFace (augmentedDart G u v hne x) (augmentedDart G u v hne y)) :
    (deletedRotation G u v hne hmiss r).SameFace
      (chordCollapse d e x) (chordCollapse d e y) := by
  have hneq : d ≠ e := by
    intro h
    exact hne (hds.symm.trans ((congrArg (fun a : G.Dart => a.fst) h).trans hes))
  have hr := insertedRotation_deletedRotation G u v hne hmiss r d e hds hes hd he
  change r.facePerm.SameCycle _ _ at hxy
  rw [← hr, insertedRotation_facePerm] at hxy
  have hp := sameCycle_reflect
    (PlaneTopology.PlanePermutationSurgery.chordPerm (deletedRotation G u v hne hmiss r).facePerm d e)
    _ (augmentedDartEquiv G u v hne hmiss) (augmentedDartEquiv G u v hne hmiss).injective
    (fun a => by simp) hxy
  exact sameCycle_chordPerm_collapse _ d e hneq hde hp

/-- Deleting an edge can lose at most one face. The proof reconstructs the
original rotation and invokes the unrestricted chord count bound. -/
theorem numFaces_le_deleted_add_one (R : FaithfulRotationSystem (G ⊔ edge u v))
    (hG : G.Connected) :
    R.toRotationSystem.numFaces ≤ (deletedRotation G u v hne hmiss R.toRotationSystem).numFaces + 1 := by
  obtain ⟨d, hds, hd⟩ := exists_forward_successor G u v hne hmiss R hG
  obtain ⟨e, hes, he⟩ := exists_reverse_successor G u v hne hmiss R hG
  have hde : d ≠ e := by
    intro h
    exact hne (hds.symm.trans ((congrArg (fun a : G.Dart => a.fst) h).trans hes))
  let r := deletedRotation G u v hne hmiss R.toRotationSystem
  have hr := insertedRotation_deletedRotation G u v hne hmiss R.toRotationSystem d e hds hes hd he
  calc R.toRotationSystem.numFaces
      = (insertedRotation G u v r d e hne hmiss hds hes).numFaces := congrArg _ hr.symm
    _ = (PlaneTopology.PlanePermutationSurgery.chordPerm r.facePerm d e).cycleType.card := by
      rw [numFaces_eq_cycleType_card, insertedRotation_facePerm,
        PlaneTopology.PlanePermutationSurgery.cycleType_permCongr]
    _ ≤ r.facePerm.cycleType.card + 1 :=
      PlaneTopology.PlaneChordCountBound.cycleType_card_chordPerm_le r.facePerm d e hde
        (r.facePerm_ne_self d) (r.facePerm_ne_self e)
    _ = r.numFaces + 1 := by rw [numFaces_eq_cycleType_card]

/-- Actual connected faithful cellular map remaining after edge deletion. -/
noncomputable def deletedCellularMap (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) : ConnectedCellularMap G where
  rotation := deletedFaithfulRotation G u v hne hmiss M.rotation
  connected := hG
  dartNonempty := ⟨(exists_dart_of_connected G u v hne hG u).choose⟩

/-- Delete a missing-edge augmentation from an arbitrary supplied plane map.
The map is not assumed to have been produced by the insertion construction.
Connectedness of the remaining graph forces exact Euler after deletion. -/
noncomputable def deleteInsertedEdgePlaneMap (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) : ConnectedPlaneMap G where
  toConnectedCellularMap := deletedCellularMap G u v hne hmiss M hG
  euler := by
    have hupper := PlaneTopology.CellularEuler.euler_le (deletedCellularMap G u v hne hmiss M hG)
    have hface := numFaces_le_deleted_add_one G u v hne hmiss M.rotation hG
    have hcard := G.card_edgeFinset_sup_edge hmiss hne
    have hold := M.euler
    change Fintype.card V + (deletedRotation G u v hne hmiss M.rawRotation).numFaces = _
    change Fintype.card V + (deletedRotation G u v hne hmiss M.rawRotation).numFaces ≤
      G.edgeFinset.card + 2 at hupper
    change M.rawRotation.numFaces ≤
      (deletedRotation G u v hne hmiss M.rawRotation).numFaces + 1 at hface
    change Fintype.card V + M.rawRotation.numFaces = _ at hold
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hupper hcard hold ⊢
    omega

/-- Exactly one face is lost when the remaining graph is connected. -/
theorem numFaces_eq_deleted_add_one (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) :
    M.rawRotation.numFaces = (deletedRotation G u v hne hmiss M.rawRotation).numFaces + 1 := by
  have hnew := (deleteInsertedEdgePlaneMap G u v hne hmiss M hG).euler
  have hold := M.euler
  have hcard := G.card_edgeFinset_sup_edge hmiss hne
  change Fintype.card V + (deletedRotation G u v hne hmiss M.rawRotation).numFaces = _ at hnew
  change Fintype.card V + M.rawRotation.numFaces = _ at hold
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hnew hold hcard
  omega

/-- The actual surviving successor corners of the deleted edge lie on the
one face exposed by deletion. This is derived from Euler, not assumed. -/
theorem deleted_corners_sameFace (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) (d e : G.Dart) (hds : d.fst = u) (hes : e.fst = v)
    (hd : pulledPerm G u v hne hmiss M.rawRotation (Sum.inr false) = Sum.inl d)
    (he : pulledPerm G u v hne hmiss M.rawRotation (Sum.inr true) = Sum.inl e) :
    (deletedRotation G u v hne hmiss M.rawRotation).SameFace d e := by
  have hneq : d ≠ e := by
    intro h
    exact hne (hds.symm.trans ((congrArg (fun a : G.Dart => a.fst) h).trans hes))
  let r := deletedRotation G u v hne hmiss M.rawRotation
  have hr := insertedRotation_deletedRotation G u v hne hmiss M.rawRotation d e hds hes hd he
  apply PlaneTopology.PlaneChordCountExact.sameCycle_of_cycleType_card_chordPerm r.facePerm d e hneq
    (r.facePerm_ne_self d) (r.facePerm_ne_self e)
  calc (PlaneTopology.PlanePermutationSurgery.chordPerm r.facePerm d e).cycleType.card
      = (insertedRotation G u v r d e hne hmiss hds hes).numFaces := by
        rw [numFaces_eq_cycleType_card, insertedRotation_facePerm,
          PlaneTopology.PlanePermutationSurgery.cycleType_permCongr]
    _ = M.rawRotation.numFaces := congrArg _ hr
    _ = r.numFaces + 1 := numFaces_eq_deleted_add_one G u v hne hmiss M hG
    _ = r.facePerm.cycleType.card + 1 := by rw [numFaces_eq_cycleType_card]

/-- Deletion exposes a genuine face containing both endpoints, with the
corners characterized as the original successors of the removed darts. -/
theorem exists_deleted_corners (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) : ∃ d e : G.Dart, d.fst = u ∧ e.fst = v ∧
      pulledPerm G u v hne hmiss M.rawRotation (Sum.inr false) = Sum.inl d ∧
      pulledPerm G u v hne hmiss M.rawRotation (Sum.inr true) = Sum.inl e ∧
      (deletedRotation G u v hne hmiss M.rawRotation).SameFace d e := by
  obtain ⟨d, hds, hd⟩ := exists_forward_successor G u v hne hmiss M.rotation hG
  obtain ⟨e, hes, he⟩ := exists_reverse_successor G u v hne hmiss M.rotation hG
  exact ⟨d, e, hds, hes, hd, he,
    deleted_corners_sameFace G u v hne hmiss M hG d e hds hes hd he⟩

/-- Every original same-face relation between surviving actual darts remains
true after deletion. The proof traces the concrete merged facial cycles. -/
theorem sameFace_deleted_of_sameFace (M : ConnectedPlaneMap (G ⊔ edge u v))
    (hG : G.Connected) (x y : G.Dart)
    (hxy : M.rawRotation.SameFace (augmentedDart G u v hne (Sum.inl x))
      (augmentedDart G u v hne (Sum.inl y))) :
    (deleteInsertedEdgePlaneMap G u v hne hmiss M hG).rawRotation.SameFace x y := by
  obtain ⟨d, e, hds, hes, hd, he, hde⟩ := exists_deleted_corners G u v hne hmiss M hG
  exact deletedRotation_sameFace_of_sameFace G u v hne hmiss M.rawRotation
    d e hds hes hd he hde (Sum.inl x) (Sum.inl y) hxy

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restoring an actually deleted edge recovers the original graph exactly. -/
theorem restore_deleted_edge (huv : G.Adj u v) :
    G.deleteEdges {s(u, v)} ⊔ edge u v = G := by
  change G \ edge u v ⊔ edge u v = G
  exact sdiff_sup_cancel ((edge_le_iff G).mpr (Or.inr huv))

/-- Delete an actual edge of a supplied connected plane map whenever the
remaining graph is connected. No surviving-dart or geometric provider is assumed. -/
noncomputable def deleteEdgePlaneMap (M : ConnectedPlaneMap G) (huv : G.Adj u v)
    (hconn : (G.deleteEdges {s(u, v)}).Connected) :
    ConnectedPlaneMap (G.deleteEdges {s(u, v)}) := by
  let H := G.deleteEdges {s(u, v)}
  have hneq : u ≠ v := G.ne_of_adj huv
  have hmissing : ¬ H.Adj u v := by simp [H]
  have heq : H ⊔ edge u v = G := restore_deleted_edge G u v huv
  let e : G ≃g (H ⊔ edge u v) := by
    rw [heq]
  exact deleteInsertedEdgePlaneMap H u v hneq hmissing (PlaneTopology.PlaneGeneralTransport.planeMap e M) hconn

end PlaneTopology.PlaneEdgeDeletion

#print axioms PlaneTopology.PlaneEdgeDeletion.deletedFaithfulRotation
#print axioms PlaneTopology.PlaneEdgeDeletion.deleteEdgePlaneMap
#print axioms PlaneTopology.PlaneEdgeDeletion.deletedRotation_sameFace_of_sameFace
#print axioms PlaneTopology.PlaneEdgeDeletion.exists_deleted_corners
#print axioms PlaneTopology.PlaneEdgeDeletion.sameFace_deleted_of_sameFace
