import Paper.Optimality.Treewidth.SevenCliqueEightExteriorSize
namespace Paper.CliqueTwoVertexBoundary
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- A two-vertex set with boundary at most seven and minimum ambient degree
eight is complete to its boundary. -/
theorem complete_boundary (X : Set V) (hX : (vertices X).card = 2)
    (hb : (boundary G X).card ≤ 7) (hd : ∀ x ∈ X, 8 ≤ G.degree x) :
    ∀ x ∈ X, ∀ y ∈ boundary G X, G.Adj x y := by
  classical
  intro x hx y hy
  have hxF : x ∈ vertices X := (mem_vertices X x).mpr hx
  have hs : G.neighborFinset x ⊆ ((vertices X).erase x) ∪ boundary G X := by
    intro z hz
    have hxz := (G.mem_neighborFinset x z).mp hz
    by_cases hzX : z ∈ X
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxz.ne.symm,(mem_vertices X z).mpr hzX⟩)
    · exact Finset.mem_union_right _ ((mem_boundary G X z).mpr ⟨hzX,x,hx,hxz.symm⟩)
  have hc := Finset.card_union_le ((vertices X).erase x) (boundary G X)
  rw [Finset.card_erase_of_mem hxF,hX] at hc
  have hd' := hd x hx
  have he : G.neighborFinset x = ((vertices X).erase x) ∪ boundary G X := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [G.card_neighborFinset_eq_degree]
    omega
  exact (G.mem_neighborFinset x y).mp (he ▸ Finset.mem_union_right _ hy)

theorem boundary_seven (X : Set V) (hX : (vertices X).card = 2)
    (hb : (boundary G X).card ≤ 7) (hd : ∀ x ∈ X, 8 ≤ G.degree x) :
    (boundary G X).card = 7 := by
  classical
  have hpos : 0 < (vertices X).card := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
  have hh := SevenCliqueEightExteriorSize.order_boundary G X
    ⟨x,(mem_vertices X x).mp hx⟩ 8 hd
  omega

end Paper.CliqueTwoVertexBoundary

