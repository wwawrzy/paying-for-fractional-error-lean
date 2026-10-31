import GraphTheory.Surfaces.SignedRotationComponentClasses

/-! Euler characteristic and Euler genus are additive over actual component
restrictions. Isolated vertices contribute zero under the flag convention. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G) [Fintype G.ConnectedComponent]

theorem eulerCharacteristic_sum :
    r.eulerCharacteristic = ∑ c : G.ConnectedComponent,
      (r.restrictComponent c).eulerCharacteristic := by
  unfold eulerCharacteristic
  rw [r.vertex_card_sum, r.edge_card_sum, r.face_card_sum]
  simp only [Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem eulerGenus_sum :
    r.eulerGenus = ∑ c : G.ConnectedComponent, (r.restrictComponent c).eulerGenus := by
  unfold eulerGenus
  rw [r.component_card_sum, r.eulerCharacteristic_sum]
  simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_sub_distrib]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.eulerCharacteristic_sum
#print axioms SimpleGraph.SignedRotation.eulerGenus_sum
