import GraphTheory.Plane.PlaneEdgeGluingRotation

/-! # Removing the duplicate edge from the actual faithful full splice -/

noncomputable section

namespace PlaneTopology.PlaneEdgeGluingRestriction

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneEdgeGluingGraph PlaneTopology.PlaneEdgeGluingDarts PlaneTopology.PlaneEdgeGluingRotation
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlanePermutationDeletion

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

local instance : Fintype (RightSurvivor R) := by classical unfold RightSurvivor; infer_instance
local instance : DecidableEq (RightSurvivor R) := Classical.decEq _

/-- Pull the full splice back to surviving darts plus the duplicate edge. -/
def pulledRotation (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Perm (GluedDart L R ⊕ Bool) :=
  (expandedDartEquiv L R hR).symm.permCongr (splicedRotation L R l r hL hR)

/-- Bypass both duplicate darts in the vertex rotation. -/
def erasedRotation (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Perm (GluedDart L R ⊕ Bool) :=
  erasePoint (erasePoint (pulledRotation L R l r hL hR) (Sum.inr true)) (Sum.inr false)

/-- Both bypassed duplicate darts are fixed. -/
theorem erasedRotation_fixed (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (b : Bool) :
    erasedRotation L R l r hL hR (Sum.inr b) = Sum.inr b := by
  cases b with
  | false => exact erasePoint_fixed _ _
  | true =>
    rw [erasedRotation, erasePoint_apply_of_ne _ _ _ (by simp) (by rw [erasePoint_fixed]; simp),
      erasePoint_fixed]

/-- The genuine vertex permutation on surviving darts. -/
def survivingRotation (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Perm (GluedDart L R) :=
  restrictLeft (erasedRotation L R l r hL hR) (erasedRotation_fixed L R l r hL hR)

/-- Source on the pulled full dart domain. -/
def expandedSource (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (x : GluedDart L R ⊕ Bool) :
    Fin 2 ⊕ (A ⊕ B) := fullSource L R (expandedDartEquiv L R hR x)

theorem expandedSource_inl (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (x : GluedDart L R) :
    expandedSource L R hR (Sum.inl x) = (gluedDart L R x).fst := by
  cases x <;> rfl

theorem pulledRotation_source (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (x : GluedDart L R ⊕ Bool) :
    expandedSource L R hR (pulledRotation L R l r hL hR x) = expandedSource L R hR x := by
  simp only [expandedSource, pulledRotation, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  exact splicedRotation_source L R l r hL hR _

/-- Bypassing duplicate darts preserves the actual graph source. -/
theorem survivingRotation_source (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (x : GluedDart L R) :
    (gluedDart L R (survivingRotation L R l r hL hR x)).fst = (gluedDart L R x).fst := by
  rw [← expandedSource_inl L R hR, survivingRotation, restrictLeft_inl_apply,
    erasedRotation]
  rw [erasePoint_preserves _ _ _ (erasePoint_preserves _ _ _ (pulledRotation_source L R l r hL hR)),
    expandedSource_inl]

/-- Cyclic source fibres survive both bypasses and restriction to old darts. -/
theorem survivingRotation_sameCycle_at_source (l : FaithfulRotationSystem L)
    (r : FaithfulRotationSystem R)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    {x y : GluedDart L R} (hs : (gluedDart L R x).fst = (gluedDart L R y).fst) :
    (survivingRotation L R l.toRotationSystem r.toRotationSystem hL hR).SameCycle x y := by
  apply restrictLeft_sameCycle
  apply erasePoint_sameCycle _ _ (by simp) (by simp)
  apply erasePoint_sameCycle _ _ (by simp) (by simp)
  have hs' : expandedSource L R hR (Sum.inl x) = expandedSource L R hR (Sum.inl y) := by
    simpa only [expandedSource_inl] using hs
  have hfull := splicedRotation_sameCycle_at_source L R l r hL hR hs'
  have hmap := sameCycle_map _ (pulledRotation L R l.toRotationSystem r.toRotationSystem hL hR)
    (expandedDartEquiv L R hR).symm (fun z => by simp [pulledRotation]) hfull
  simpa only [Equiv.symm_apply_apply] using hmap

/-- The actual source-preserving rotation on the exact simple graph union. -/
def gluedRotation (l : L.RotationSystem) (r : R.RotationSystem)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (gluedGraph L R).RotationSystem where
  σ := (gluedDartEquiv L R hL).permCongr (survivingRotation L R l r hL hR)
  σ_source x := by
    obtain ⟨x, rfl⟩ := (gluedDartEquiv L R hL).surjective x
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact survivingRotation_source L R l r hL hR x

/-- The graph union has a constructed faithful rotation, not an assumed one. -/
def gluedFaithfulRotation (l : FaithfulRotationSystem L) (r : FaithfulRotationSystem R)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    FaithfulRotationSystem (gluedGraph L R) where
  toRotationSystem := gluedRotation L R l.toRotationSystem r.toRotationSystem hL hR
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro v x hx y hy
    obtain ⟨x, rfl⟩ := (gluedDartEquiv L R hL).surjective x
    obtain ⟨y, rfl⟩ := (gluedDartEquiv L R hL).surjective y
    apply sameCycle_map (survivingRotation L R l.toRotationSystem r.toRotationSystem hL hR)
      _ (gluedDartEquiv L R hL) (fun z => by simp [gluedRotation])
    exact survivingRotation_sameCycle_at_source L R l r hL hR (hx.trans hy.symm)

#print axioms gluedFaithfulRotation

end PlaneTopology.PlaneEdgeGluingRestriction
