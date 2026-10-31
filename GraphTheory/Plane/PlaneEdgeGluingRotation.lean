import GraphTheory.Plane.PlaneEdgeGluingDarts
import GraphTheory.Plane.PlaneEdgeGluingPermutation

/-! # Joining the actual vertex cycles at both ends of a common edge -/

noncomputable section

namespace PlaneTopology.PlaneEdgeGluingRotation

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneEdgeGluingGraph PlaneTopology.PlaneEdgeGluingDarts
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneEdgeGluingPermutation
open PlaneTopology.PlaneChordCountBound

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

/-- Source labels on the full disjoint sum, with the two endpoints identified. -/
def fullSource : L.Dart ⊕ R.Dart → Fin 2 ⊕ (A ⊕ B) :=
  Sum.elim (fun d => leftVertex d.fst) (fun d => rightVertex d.fst)

/-- Initial disjoint vertex rotation. -/
def fullRotation (l : L.RotationSystem) (r : R.RotationSystem) : Perm (L.Dart ⊕ R.Dart) :=
  Equiv.sumCongr l.σ r.σ

theorem fullRotation_source (l : L.RotationSystem) (r : R.RotationSystem)
    (x : L.Dart ⊕ R.Dart) :
    fullSource L R (fullRotation L R l r x) = fullSource L R x := by
  cases x with
  | inl d => change leftVertex (l.σ d).fst = _; rw [l.σ_source]; rfl
  | inr d => change rightVertex (r.σ d).fst = _; rw [r.σ_source]; rfl

/-- Distinguished left and right copies of the two common-edge orientations. -/
def leftCommon (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) : L.Dart ⊕ R.Dart :=
  Sum.inl (rightCommonDart L hL b)

def rightCommon (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) : L.Dart ⊕ R.Dart :=
  Sum.inr (rightCommonDart R hR b)

/-- At endpoint zero splice before the distinguished darts. -/
def firstSplice (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Perm (L.Dart ⊕ R.Dart) :=
  fullRotation L R l r * swap (leftCommon L R hL false) (rightCommon L R hR false)

/-- At endpoint one splice after the reversed distinguished darts. -/
def splicedRotation (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Perm (L.Dart ⊕ R.Dart) :=
  swap (leftCommon L R hL true) (rightCommon L R hR true) * firstSplice L R l r hL hR

theorem common_not_sameCycle_full (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (b c : Bool) :
    ¬(fullRotation L R l r).SameCycle (leftCommon L R hL b) (rightCommon L R hR c) := by
  intro h
  have heq := sameCycle_label (fullRotation L R l r) Sum.isLeft
    (fun x => by cases x <;> rfl) h
  simp [leftCommon, rightCommon] at heq

/-- A label which merges the left and right side only at endpoint zero. -/
def firstLabel (x : L.Dart ⊕ R.Dart) : Option Bool :=
  if fullSource L R x = Sum.inl 0 then none else some x.isLeft

theorem firstSplice_label (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (x : L.Dart ⊕ R.Dart) :
    firstLabel L R (firstSplice L R l r hL hR x) = firstLabel L R x := by
  have hfull (z : L.Dart ⊕ R.Dart) :
      firstLabel L R (fullRotation L R l r z) = firstLabel L R z := by
    simp only [firstLabel, fullRotation_source]
    cases z <;> rfl
  rw [firstSplice, mul_apply, hfull]
  apply map_swap_eq
  simp [firstLabel, fullSource, leftCommon, rightCommon, rightCommonDart, leftVertex, rightVertex]

/-- The second splice still joins different vertex cycles: the first affected
only endpoint zero, not endpoint one. -/
theorem common_not_sameCycle_first (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    ¬(firstSplice L R l r hL hR).SameCycle
      (leftCommon L R hL true) (rightCommon L R hR true) := by
  intro h
  have heq := sameCycle_label _ (firstLabel L R) (firstSplice_label L R l r hL hR) h
  simp [firstLabel, fullSource, leftCommon, rightCommon, rightCommonDart, leftVertex, rightVertex] at heq

/-- Both splices preserve all original vertex-cycle relations. -/
theorem splicedRotation_sameCycle_old (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    {x y : L.Dart ⊕ R.Dart} (hxy : (fullRotation L R l r).SameCycle x y) :
    (splicedRotation L R l r hL hR).SameCycle x y := by
  apply sameCycle_swap_mul_preserved _ _ _ (common_not_sameCycle_first L R l r hL hR)
  exact sameCycle_mul_swap_preserved _ _ _ (common_not_sameCycle_full L R l r hL hR false false) hxy

/-- The two formerly separate cycles at either common endpoint really join. -/
theorem splicedRotation_sameCycle_common (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) :
    (splicedRotation L R l r hL hR).SameCycle
      (leftCommon L R hL b) (rightCommon L R hR b) := by
  cases b with
  | false =>
    apply sameCycle_swap_mul_preserved _ _ _ (common_not_sameCycle_first L R l r hL hR)
    exact sameCycle_mul_swap_ends _ _ _ (common_not_sameCycle_full L R l r hL hR false false)
  | true =>
    exact sameCycle_swap_mul_of_not_sameCycle _ _ _ (common_not_sameCycle_first L R l r hL hR)

/-- The actual splice preserves the source of every full dart. -/
theorem splicedRotation_source (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (x : L.Dart ⊕ R.Dart) :
    fullSource L R (splicedRotation L R l r hL hR x) = fullSource L R x := by
  have hcommon (b : Bool) : fullSource L R (leftCommon L R hL b) =
      fullSource L R (rightCommon L R hR b) := by
    cases b <;> rfl
  rw [splicedRotation, mul_apply, map_swap_eq _ _ _ _ (hcommon true), firstSplice,
    mul_apply, fullRotation_source, map_swap_eq _ _ _ _ (hcommon false)]

/-- Every source fibre in the full splice is one actual permutation cycle. -/
theorem splicedRotation_sameCycle_at_source (l : FaithfulRotationSystem L)
    (r : FaithfulRotationSystem R)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    {x y : L.Dart ⊕ R.Dart} (hsource : fullSource L R x = fullSource L R y) :
    (splicedRotation L R l.toRotationSystem r.toRotationSystem hL hR).SameCycle x y := by
  let p := splicedRotation L R l.toRotationSystem r.toRotationSystem hL hR
  have hl (x y : L.Dart) (hs : x.fst = y.fst) : p.SameCycle (Sum.inl x) (Sum.inl y) := by
    apply splicedRotation_sameCycle_old
    exact sameCycle_map l.toRotationSystem.σ (fullRotation L R l.toRotationSystem r.toRotationSystem)
      Sum.inl (fun _ => rfl) (l.sameCycle_at_source hs)
  have hr (x y : R.Dart) (hs : x.fst = y.fst) : p.SameCycle (Sum.inr x) (Sum.inr y) := by
    apply splicedRotation_sameCycle_old
    exact sameCycle_map r.toRotationSystem.σ (fullRotation L R l.toRotationSystem r.toRotationSystem)
      Sum.inr (fun _ => rfl) (r.sameCycle_at_source hs)
  have hc (x : L.Dart) (y : R.Dart) (hs : leftVertex x.fst = rightVertex y.fst) :
      p.SameCycle (Sum.inl x) (Sum.inr y) := by
    obtain ⟨i, hx, hy⟩ := (leftVertex_eq_rightVertex_iff x.fst y.fst).mp hs
    fin_cases i
    · exact (hl x (rightCommonDart L hL false) hx).trans
        ((splicedRotation_sameCycle_common L R l.toRotationSystem r.toRotationSystem hL hR false).trans
          (hr y (rightCommonDart R hR false) hy).symm)
    · exact (hl x (rightCommonDart L hL true) hx).trans
        ((splicedRotation_sameCycle_common L R l.toRotationSystem r.toRotationSystem hL hR true).trans
          (hr y (rightCommonDart R hR true) hy).symm)
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hl x y (leftVertex_injective hsource)
    | inr y => exact hc x y hsource
  | inr x =>
    cases y with
    | inl y => exact (hc y x hsource.symm).symm
    | inr y => exact hr x y (rightVertex_injective hsource)

#print axioms splicedRotation_sameCycle_common
#print axioms splicedRotation_source
#print axioms splicedRotation_sameCycle_at_source

end PlaneTopology.PlaneEdgeGluingRotation
