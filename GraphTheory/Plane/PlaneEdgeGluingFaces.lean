import GraphTheory.Plane.PlaneEdgeGluingRestriction
import GraphTheory.Plane.PlaneEdgeInsertion

/-! # Exact facial identities for removing the duplicate common edge -/

noncomputable section

namespace PlaneTopology.PlaneEdgeGluingFaces

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneEdgeGluingGraph PlaneTopology.PlaneEdgeGluingDarts PlaneTopology.PlaneEdgeGluingRotation
open PlaneTopology.PlaneEdgeGluingRestriction PlaneTopology.PlanePermutationSurgery PlaneTopology.PlanePermutationDeletion
open PlaneTopology.PlaneEdgeGluingPermutation

/-- Exact inverse of bypassing the two fresh vertex-rotation positions. -/
theorem reconstruct_face_after_two_erases {α : Type*} [DecidableEq α]
    (p : Perm (α ⊕ Bool)) (q t : Perm α) (a b : α)
    (ha : p (Sum.inr false) = Sum.inl a) (hb : p (Sum.inr true) = Sum.inl b)
    (hq : Equiv.sumCongr q (Equiv.refl Bool) =
      erasePoint (erasePoint p (Sum.inr true)) (Sum.inr false)) :
    chordPerm (q * t) a b = p * Equiv.sumCongr t (swap false true) := by
  have hs : erasePoint p (Sum.inr true) (Sum.inr false) = Sum.inl a := by
    rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [ha]; simp), ha]
  have hrot : swap (Sum.inl b) (Sum.inr true) *
      (swap (Sum.inl a) (Sum.inr false) * Equiv.sumCongr q (Equiv.refl Bool)) = p := by
    rw [hq, erasePoint, hs, erasePoint, hb,
      swap_comm (Sum.inr false) (Sum.inl a), swap_comm (Sum.inr true) (Sum.inl b)]
    simp only [← mul_assoc, swap_mul_self, one_mul]
  rw [← hrot, mul_assoc, mul_assoc]
  unfold chordPerm
  congr 2
  ext x
  cases x <;> rfl

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

local instance : Fintype (RightSurvivor R) := by classical unfold RightSurvivor; infer_instance
local instance : DecidableEq (RightSurvivor R) := Classical.decEq _

/-- Reversal on the full disjoint dart sum. -/
def fullReversal : Perm (L.Dart ⊕ R.Dart) := Equiv.sumCongr (dartSymmPerm L) (dartSymmPerm R)

theorem fullReversal_involutive : Function.Involutive (fullReversal L R) := by
  intro x
  cases x <;> rfl

/-- Before deleting the duplicate edge, the facial cycle type is the disjoint sum. -/
theorem spliced_face_cycleType (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (splicedRotation L R l r hL hR * fullReversal L R).cycleType =
      l.facePerm.cycleType + r.facePerm.cycleType := by
  have h := cycleType_splice_face (fullRotation L R l r) (fullReversal L R)
    (leftCommon L R hL false) (rightCommon L R hR false) (fullReversal_involutive L R)
  change (splicedRotation L R l r hL hR * fullReversal L R).cycleType = _ at h
  rw [h]
  have heq : fullRotation L R l r * fullReversal L R = Equiv.sumCongr l.facePerm r.facePerm := by
    ext x
    cases x <;> rfl
  rw [heq, cycleType_sumCongr]

/-- Pulling reversal back keeps exactly the surviving reversal and the fresh swap. -/
theorem pulled_reversal (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (expandedDartEquiv L R hR).symm.permCongr (fullReversal L R) =
      Equiv.sumCongr (gluedReversal L R) (swap false true) := by
  ext x
  apply (expandedDartEquiv L R hR).injective
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact (expandedDart_reversal L R hR x).symm

/-- The full pulled face permutation still has the sum of the old cycle types. -/
theorem pulled_face_cycleType (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (pulledRotation L R l r hL hR * Equiv.sumCongr (gluedReversal L R) (swap false true)).cycleType =
      l.facePerm.cycleType + r.facePerm.cycleType := by
  rw [← pulled_reversal L R hR, pulledRotation, ← Equiv.permCongr_mul,
    cycleType_permCongr, spliced_face_cycleType]

/-- Neither duplicated dart is fixed by the full spliced vertex rotation. -/
theorem splicedRotation_common_moved (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) :
    splicedRotation L R l r hL hR (rightCommon L R hR b) ≠ rightCommon L R hR b := by
  cases b with
  | false =>
    have hfix : swap (leftCommon L R hL true) (rightCommon L R hR true)
        (rightCommon L R hR false) = rightCommon L R hR false := by
      simp [leftCommon, rightCommon, rightCommonDart, swap_apply_def]
    intro h
    have hs : Sum.inl (l.σ (rightCommonDart L hL false)) = rightCommon L R hR false := by
      apply (swap (leftCommon L R hL true) (rightCommon L R hR true)).injective
      simpa only [splicedRotation, firstSplice, mul_apply, swap_apply_right, fullRotation,
        leftCommon, Equiv.sumCongr_apply, Sum.map_inl] using h.trans hfix.symm
    cases hs
  | true =>
    have hfix : swap (leftCommon L R hL false) (rightCommon L R hR false)
        (rightCommon L R hR true) = rightCommon L R hR true := by
      simp [leftCommon, rightCommon, rightCommonDart, swap_apply_def]
    intro h
    have hs : Sum.inr (r.σ (rightCommonDart R hR true)) = leftCommon L R hL true := by
      apply (swap (leftCommon L R hL true) (rightCommon L R hR true)).injective
      simpa only [splicedRotation, firstSplice, mul_apply, hfix, fullRotation,
        rightCommon, Equiv.sumCongr_apply, Sum.map_inr, swap_apply_left] using h
    cases hs

/-- Each removed dart has a surviving successor in the full rotation. -/
theorem pulledRotation_successor_exists (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) :
    ∃ a : GluedDart L R, pulledRotation L R l r hL hR (Sum.inr b) = Sum.inl a := by
  have hmove : pulledRotation L R l r hL hR (Sum.inr b) ≠ Sum.inr b := by
    intro h
    have heq := congrArg (expandedDartEquiv L R hR) h
    simp only [pulledRotation, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] at heq
    exact splicedRotation_common_moved L R l r hL hR b heq
  cases hs : pulledRotation L R l r hL hR (Sum.inr b) with
  | inl a => exact ⟨a, rfl⟩
  | inr c =>
    have hsource := pulledRotation_source L R l r hL hR (Sum.inr b)
    rw [hs] at hsource
    have hbc : b = c := by
      cases b <;> cases c <;> simp_all [expandedSource, expandedDartEquiv_apply, expandedDart,
        fullSource, rightCommonDart, rightVertex]
    exact (hmove (hs.trans (congrArg Sum.inr hbc.symm))).elim

/-- The actual final face permutation is the transported surviving face permutation. -/
theorem gluedRotation_facePerm (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (gluedRotation L R l r hL hR).facePerm =
      (gluedDartEquiv L R hL).permCongr (survivingRotation L R l r hL hR * gluedReversal L R) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (gluedDartEquiv L R hL).surjective x
  rw [SimpleGraph.RotationSystem.facePerm_apply]
  change (gluedRotation L R l r hL hR).σ (gluedDart L R x).symm = _
  rw [← gluedDart_reversal]
  change (gluedDartEquiv L R hL).permCongr (survivingRotation L R l r hL hR)
    (gluedDartEquiv L R hL (gluedReversal L R x)) =
    (gluedDartEquiv L R hL).permCongr (survivingRotation L R l r hL hR * gluedReversal L R)
      (gluedDartEquiv L R hL x)
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, mul_apply]

/-- Deleting the duplicate edge loses at most one actual face. The reverse
inequality needed for exactness will follow from cellular Euler. -/
theorem old_numFaces_le_glued_add_one (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    l.numFaces + r.numFaces ≤
      (by classical exact (gluedRotation L R l r hL hR).numFaces) + 1 := by
  classical
  obtain ⟨a, ha⟩ := pulledRotation_successor_exists L R l r hL hR false
  obtain ⟨b, hb⟩ := pulledRotation_successor_exists L R l r hL hR true
  have hab : a ≠ b := by
    intro h
    have heq := (pulledRotation L R l r hL hR).injective
      (ha.trans ((congrArg Sum.inl h).trans hb.symm))
    cases heq
  let q := survivingRotation L R l r hL hR * gluedReversal L R
  have hmove (x : GluedDart L R) : q x ≠ x := by
    intro h
    apply (gluedRotation L R l r hL hR).facePerm_ne_self (gluedDartEquiv L R hL x)
    rw [gluedRotation_facePerm]
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using congrArg (gluedDartEquiv L R hL) h
  have hchord := PlaneTopology.PlaneChordCountBound.cycleType_card_chordPerm_le q a b hab (hmove a) (hmove b)
  have hrec := reconstruct_face_after_two_erases (pulledRotation L R l r hL hR)
    (survivingRotation L R l r hL hR) (gluedReversal L R) a b ha hb
    (sumCongr_restrictLeft _ (erasedRotation_fixed L R l r hL hR))
  change chordPerm q a b = _ at hrec
  rw [hrec, pulled_face_cycleType, Multiset.card_add] at hchord
  have hnew : (gluedRotation L R l r hL hR).numFaces = q.cycleType.card := by
    rw [PlaneTopology.PlaneEdgeInsertion.numFaces_eq_cycleType_card, gluedRotation_facePerm, cycleType_permCongr]
  rw [hnew, PlaneTopology.PlaneEdgeInsertion.numFaces_eq_cycleType_card,
    PlaneTopology.PlaneEdgeInsertion.numFaces_eq_cycleType_card]
  exact hchord

#print axioms pulled_face_cycleType
#print axioms pulledRotation_successor_exists
#print axioms gluedRotation_facePerm
#print axioms old_numFaces_le_glued_add_one

end PlaneTopology.PlaneEdgeGluingFaces
