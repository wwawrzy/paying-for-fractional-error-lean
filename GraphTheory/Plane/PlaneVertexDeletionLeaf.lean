import GraphTheory.Plane.PlaneEdgeDeletion
import GraphTheory.Plane.PlaneLeafInsertion
import GraphTheory.Plane.PlaneChordFaces

/-! # Exact inverse leaf construction for actual connected plane maps -/

namespace PlaneTopology.PlaneVertexDeletionLeaf

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlanePermutationDeletion PlaneTopology.PlaneLeafInsertion

variable {V : Type*} (G : SimpleGraph V) (v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Pull an arbitrary actual leaf-graph rotation back to its explicit dart sum. -/
noncomputable def pulledPerm (r : (leafGraph G v).RotationSystem) : Perm (G.Dart ⊕ Bool) :=
  (leafDartEquiv G v).symm.permCongr r.σ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Pullback preserves the actual source labels. -/
theorem pulledPerm_source (r : (leafGraph G v).RotationSystem) (a : G.Dart ⊕ Bool) :
    (leafDart G v (pulledPerm G v r a)).fst = (leafDart G v a).fst := by
  change ((leafDartEquiv G v) (pulledPerm G v r a)).fst = ((leafDartEquiv G v) a).fst
  simp only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact r.σ_source _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The leaf's unique outgoing dart is fixed in every source-preserving rotation. -/
theorem pulledPerm_true (r : (leafGraph G v).RotationSystem) :
    pulledPerm G v r (Sum.inr true) = Sum.inr true := by
  have hs := pulledPerm_source G v r (Sum.inr true)
  cases hp : pulledPerm G v r (Sum.inr true) with
  | inl d => simp [hp, leafDart] at hs
  | inr b => cases b <;> simp_all [leafDart]

/-- The original faithful vertex cycles transport to the dart sum. -/
theorem pulledPerm_sameCycle (R : FaithfulRotationSystem (leafGraph G v))
    (a b : G.Dart ⊕ Bool) (hab : (leafDart G v a).fst = (leafDart G v b).fst) :
    (pulledPerm G v R.toRotationSystem).SameCycle a b := by
  have h := PlaneTopology.PlanePermutationSurgery.sameCycle_map R.toRotationSystem.σ
    (pulledPerm G v R.toRotationSystem) (leafDartEquiv G v).symm
    (fun a => by simp [pulledPerm]) (R.sameCycle_at_source hab)
  change (pulledPerm G v R.toRotationSystem).SameCycle
    ((leafDartEquiv G v).symm ((leafDartEquiv G v) a))
    ((leafDartEquiv G v).symm ((leafDartEquiv G v) b)) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Bypass the dart from the attachment vertex to the leaf. -/
noncomputable def erasedPerm (r : (leafGraph G v).RotationSystem) : Perm (G.Dart ⊕ Bool) :=
  erasePoint (pulledPerm G v r) (Sum.inr false)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Both leaf-edge darts are fixed after the single nontrivial bypass. -/
theorem erasedPerm_fixed (r : (leafGraph G v).RotationSystem) (b : Bool) :
    erasedPerm G v r (Sum.inr b) = Sum.inr b := by
  cases b
  · exact erasePoint_fixed _ _
  · rw [erasedPerm, erasePoint_apply_of_ne _ _ _ (by simp)
      (by rw [pulledPerm_true]; simp), pulledPerm_true]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The bypass still preserves actual source labels. -/
theorem erasedPerm_source (r : (leafGraph G v).RotationSystem) (a : G.Dart ⊕ Bool) :
    (leafDart G v (erasedPerm G v r a)).fst = (leafDart G v a).fst :=
  erasePoint_preserves _ _ (fun z => (leafDart G v z).fst) (pulledPerm_source G v r) a

/-- Actual rotation on the old graph after removing its fresh leaf. -/
noncomputable def deletedRotation (r : (leafGraph G v).RotationSystem) : G.RotationSystem where
  σ := restrictLeft (erasedPerm G v r) (erasedPerm_fixed G v r)
  σ_source a := by
    have h := erasedPerm_source G v r (Sum.inl a)
    rw [← restrictLeft_inl_apply _ (erasedPerm_fixed G v r)] at h
    exact Option.some.inj h

/-- Faithfulness survives the exact inverse leaf operation. -/
noncomputable def deletedFaithfulRotation (R : FaithfulRotationSystem (leafGraph G v)) :
    FaithfulRotationSystem G where
  toRotationSystem := deletedRotation G v R.toRotationSystem
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro w a ha b hb
    apply restrictLeft_sameCycle _ (erasedPerm_fixed G v R.toRotationSystem)
    apply erasePoint_sameCycle _ _ (by simp) (by simp)
    exact pulledPerm_sameCycle G v R _ _ (congrArg some (ha.trans hb.symm))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Connectedness and one old dart provide an outgoing dart at every old vertex. -/
theorem exists_dart_at (hG : G.Connected) (hD : Nonempty G.Dart) (w : V) :
    ∃ d : G.Dart, d.fst = w := by
  obtain ⟨e⟩ := hD
  haveI : Nontrivial V := ⟨⟨e.fst, e.snd, G.ne_of_adj e.adj⟩⟩
  obtain ⟨z, hwz⟩ := hG.preconnected.exists_adj_of_nontrivial w
  exact ⟨⟨(w, z), hwz⟩, rfl⟩

/-- The surviving successor of the leaf edge is an actual old attachment dart. -/
theorem exists_successor (R : FaithfulRotationSystem (leafGraph G v))
    (hG : G.Connected) (hD : Nonempty G.Dart) : ∃ d : G.Dart, d.fst = v ∧
      pulledPerm G v R.toRotationSystem (Sum.inr false) = Sum.inl d := by
  obtain ⟨a, ha⟩ := exists_dart_at G hG hD v
  have hc := pulledPerm_sameCycle G v R (Sum.inr false) (Sum.inl a) (congrArg some ha.symm)
  have hnf : pulledPerm G v R.toRotationSystem (Sum.inr false) ≠ Sum.inr false := by
    intro h
    have heq := hc.eq_of_left h
    cases heq
  have hs := pulledPerm_source G v R.toRotationSystem (Sum.inr false)
  cases hp : pulledPerm G v R.toRotationSystem (Sum.inr false) with
  | inl d => exact ⟨d, Option.some.inj (by simpa only [hp] using hs), rfl⟩
  | inr b =>
    cases b
    · exact (hnf hp).elim
    · simp [hp, leafDart] at hs

omit [Fintype V] [DecidableRel G.Adj] in
/-- Reinserting the removed leaf recovers the original vertex permutation. -/
theorem leafVertexPerm_deletedRotation (r : (leafGraph G v).RotationSystem) (d : G.Dart)
    (hd : pulledPerm G v r (Sum.inr false) = Sum.inl d) :
    leafVertexPerm G (deletedRotation G v r) d = pulledPerm G v r := by
  have hq := sumCongr_restrictLeft (erasedPerm G v r) (erasedPerm_fixed G v r)
  change Equiv.sumCongr (deletedRotation G v r).σ (Equiv.refl Bool) =
    erasePoint (pulledPerm G v r) (Sum.inr false) at hq
  rw [leafVertexPerm, hq, erasePoint, hd, Equiv.swap_comm (Sum.inr false) (Sum.inl d)]
  simp [← mul_assoc]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Exact reconstruction of the original actual leaf rotation. -/
theorem leafRotation_deletedRotation (r : (leafGraph G v).RotationSystem) (d : G.Dart)
    (hds : d.fst = v) (hd : pulledPerm G v r (Sum.inr false) = Sum.inl d) :
    leafRotation G v (deletedRotation G v r) d hds = r := by
  apply PlaneTopology.PlaneEdgeDeletion.rotation_eq_of_sigma_eq
  apply Equiv.ext
  intro a
  change (leafDartEquiv G v) (leafVertexPerm G (deletedRotation G v r) d
    ((leafDartEquiv G v).symm a)) = r.σ a
  rw [leafVertexPerm_deletedRotation G v r d hd]
  simp only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Removing a genuine leaf leaves the number of actual faces unchanged. -/
theorem numFaces_deleted (M : ConnectedPlaneMap (leafGraph G v))
    (hG : G.Connected) (hD : Nonempty G.Dart) :
    (deletedRotation G v M.rawRotation).numFaces = M.rawRotation.numFaces := by
  obtain ⟨d, hds, hd⟩ := exists_successor G v M.rotation hG hD
  exact (leafRotation_numFaces G v (deletedRotation G v M.rawRotation) d hds).symm.trans
    (congrArg _ (leafRotation_deletedRotation G v M.rawRotation d hds hd))

/-- Remove a fresh leaf from any supplied actual connected plane map. -/
noncomputable def deleteLeafPlaneMap (M : ConnectedPlaneMap (leafGraph G v))
    (hG : G.Connected) (hD : Nonempty G.Dart) : ConnectedPlaneMap G where
  rotation := deletedFaithfulRotation G v M.rotation
  connected := hG
  dartNonempty := hD
  euler := by
    have hold := M.euler
    have hc := card_edges_leafGraph G v
    have hf := numFaces_deleted G v M hG hD
    change Fintype.card V + (deletedRotation G v M.rawRotation).numFaces = _
    change Fintype.card (Option V) + M.rawRotation.numFaces = _ at hold
    rw [Fintype.card_option] at hold
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hold hc ⊢
    omega

/-- Collapse both leaf-edge darts to the old attachment corner. -/
def leafCollapse (d : G.Dart) : G.Dart ⊕ Bool → G.Dart := Sum.elim id (fun _ => d)

/-- Removing the two inserted leaf darts preserves every actual facial orbit. -/
theorem sameCycle_leafFacePerm_collapse (r : G.RotationSystem) (d : G.Dart)
    {x y : G.Dart ⊕ Bool} (hxy : (leafFacePerm G r d).SameCycle x y) :
    r.facePerm.SameCycle (leafCollapse G d x) (leafCollapse G d y) := by
  apply sameCycle_map_of_steps _ r.facePerm (leafCollapse G d) _ hxy
  intro z
  cases z with
  | inl z =>
    have hz : r.facePerm.SameCycle z (r.facePerm z) := ⟨1, by simp⟩
    by_cases hd : r.σ z.symm = d <;>
      simpa [leafFacePerm, mul_apply, Equiv.swap_apply_def, leafCollapse, hd] using hz
  | inr z =>
    cases z <;> simp [leafFacePerm, mul_apply, Equiv.swap_apply_def, leafCollapse, SameCycle.refl]

/-- All original incidences collapse to incidences of the exact deleted map. -/
theorem deletedRotation_sameFace (r : (leafGraph G v).RotationSystem) (d : G.Dart)
    (hds : d.fst = v) (hd : pulledPerm G v r (Sum.inr false) = Sum.inl d)
    (x y : G.Dart ⊕ Bool) (hxy : r.SameFace (leafDart G v x) (leafDart G v y)) :
    (deletedRotation G v r).SameFace (leafCollapse G d x) (leafCollapse G d y) := by
  have hr := leafRotation_deletedRotation G v r d hds hd
  change r.facePerm.SameCycle _ _ at hxy
  rw [← hr, leafRotation_facePerm] at hxy
  have hp := sameCycle_reflect (leafFacePerm G (deletedRotation G v r) d) _
    (leafDartEquiv G v) (leafDartEquiv G v).injective (fun a => by simp) hxy
  exact sameCycle_leafFacePerm_collapse G _ d hp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The one outgoing leaf dart is the only possible witness at `none`. -/
theorem dart_eq_true_of_source_none (a : (leafGraph G v).Dart) (ha : a.fst = none) :
    a = leafDart G v (Sum.inr true) := by
  obtain ⟨z, rfl⟩ := (leafDartEquiv G v).surjective a
  cases z with
  | inl z => cases ha
  | inr z => cases z <;> first | rfl | cases ha

/-- Every old vertex cofacial with the former leaf lies on one common actual
face after deletion; this is the final invariant for apex removal. -/
theorem exists_common_face_after_leaf (M : ConnectedPlaneMap (leafGraph G v))
    (hG : G.Connected) (hD : Nonempty G.Dart) :
    ∃ base : G.Dart, ∀ w : V,
      PlaneTopology.PlaneChordFaces.CoFacial (leafGraph G v) M.rawRotation none (some w) →
      ∃ e : G.Dart, e.fst = w ∧ (deleteLeafPlaneMap G v M hG hD).rawRotation.SameFace base e := by
  obtain ⟨d, hds, hd⟩ := exists_successor G v M.rotation hG hD
  refine ⟨d, ?_⟩
  intro w hw
  obtain ⟨a, b, ha, hb, hab⟩ := hw
  rw [dart_eq_true_of_source_none G v a ha] at hab
  obtain ⟨z, rfl⟩ := (leafDartEquiv G v).surjective b
  have hface := deletedRotation_sameFace G v M.rawRotation d hds hd (Sum.inr true) z hab
  cases z with
  | inl e => exact ⟨e, Option.some.inj hb, hface⟩
  | inr z =>
    cases z
    · exact ⟨d, hds.trans (Option.some.inj hb), SameCycle.refl _ _⟩
    · cases hb

end PlaneTopology.PlaneVertexDeletionLeaf

#print axioms PlaneTopology.PlaneVertexDeletionLeaf.deleteLeafPlaneMap
#print axioms PlaneTopology.PlaneVertexDeletionLeaf.exists_common_face_after_leaf
