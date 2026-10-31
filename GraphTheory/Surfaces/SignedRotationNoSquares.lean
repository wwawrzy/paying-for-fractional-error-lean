import GraphTheory.Surfaces.SignedRotationShortFaces

/-! Connected simple graphs with at least three vertices have no four-flag faces. -/
namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem card_le_two_of_adjacent_leaves (hG : G.Connected) {u v : V}
    (huv : G.Adj u v) (hu : G.degree u = 1) (hv : G.degree v = 1) :
    Fintype.card V ≤ 2 := by
  have unique_u : ∀ w, G.Adj u w → w = v := by
    obtain ⟨z, hz, he⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
    intro w hw
    exact (he w hw).trans (he v huv).symm
  have unique_v : ∀ w, G.Adj v w → w = u := by
    obtain ⟨z, hz, he⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    intro w hw
    exact (he w hw).trans (he u huv.symm).symm
  have walk_closed : ∀ {a b : V}, G.Walk a b → a = u ∨ a = v → b = u ∨ b = v := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a w b haw p ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (unique_u w haw)
      · exact Or.inl (unique_v w haw)
  have hall : ∀ w : V, w ∈ ({u, v} : Finset V) := by
    intro w
    obtain ⟨p⟩ := hG.preconnected u w
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      walk_closed p (Or.inl rfl)
  have hc := Finset.card_le_card (show Finset.univ ⊆ ({u, v} : Finset V) from
    fun w _ => hall w)
  have hp : ({u, v} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  simpa only [Finset.card_univ] using hc.trans hp

namespace SignedRotation

theorem no_face_square (r : SignedRotation G) (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) (x : Flag G) :
    r.cornerFlip (r.edgeFlip x) ≠ r.edgeFlip (r.cornerFlip x) := by
  intro h
  obtain ⟨hu, hv⟩ := r.face_square_endpoints_degree_one x h
  have hc := card_le_two_of_adjacent_leaves hG x.1.adj hu hv
  omega

end SignedRotation
end SimpleGraph

#print axioms SimpleGraph.card_le_two_of_adjacent_leaves
#print axioms SimpleGraph.SignedRotation.no_face_square
