import GraphTheory.Surfaces.SignedRotation
import GraphTheory.Faces.FaithfulPlaneMap

/-! Untwisted signed rotations extend the existing faithful rotation systems.
On positive flags, the two-involution face step is the existing face permutation. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V}

def ofFaithful (R : PlaneTopology.Faces.FaithfulPlaneMap.FaithfulRotationSystem G) :
    SignedRotation G where
  toRotationSystem := R.toRotationSystem
  cyclic := fun _ _ h => R.sameCycle_at_source h
  twist := fun _ => false
  twist_symm := fun _ => rfl

theorem untwisted_face_step (r : SignedRotation G)
    (h : ∀ d, r.twist d = false) (d : G.Dart) :
    r.cornerFlip (r.edgeFlip (d, true)) = (r.toRotationSystem.facePerm d, true) := by
  simp [edgeFlip, cornerFlip, h, RotationSystem.facePerm_apply]

theorem ofFaithful_face_step
    (R : PlaneTopology.Faces.FaithfulPlaneMap.FaithfulRotationSystem G) (d : G.Dart) :
    (ofFaithful R).cornerFlip ((ofFaithful R).edgeFlip (d, true)) =
      (R.toRotationSystem.facePerm d, true) :=
  untwisted_face_step (ofFaithful R) (fun _ => rfl) d

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.untwisted_face_step
#print axioms SimpleGraph.SignedRotation.ofFaithful_face_step
