import Paper.Optimality.Treewidth.SevenCliqueEightExteriorSize
namespace Paper.CliqueSaturatedBoundary
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem neighbors (X : Set V) (d : ℕ)
    (hsize : (vertices X).card+(boundary G X).card ≤ d+1)
    (hd : ∀ x ∈ X, d ≤ G.degree x) (x : V) (hx : x ∈ X) :
    G.neighborFinset x = ((vertices X).erase x) ∪ boundary G X := by
  classical
  have hxF : x ∈ vertices X := (mem_vertices X x).mpr hx
  have hs : G.neighborFinset x ⊆ ((vertices X).erase x) ∪ boundary G X := by
    intro z hz
    have hxz := (G.mem_neighborFinset x z).mp hz
    by_cases hzX : z ∈ X
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxz.ne.symm,(mem_vertices X z).mpr hzX⟩)
    · exact Finset.mem_union_right _ ((mem_boundary G X z).mpr ⟨hzX,x,hx,hxz.symm⟩)
  apply Finset.eq_of_subset_of_card_le hs
  have hc := Finset.card_union_le ((vertices X).erase x) (boundary G X)
  rw [Finset.card_erase_of_mem hxF] at hc
  have hp : 0 < (vertices X).card := Finset.card_pos.mpr ⟨x,hxF⟩
  have hh := hd x hx
  rw [G.card_neighborFinset_eq_degree]
  omega

theorem clique (X : Set V) (d : ℕ)
    (hsize : (vertices X).card+(boundary G X).card ≤ d+1)
    (hd : ∀ x ∈ X, d ≤ G.degree x) : G.IsClique X := by
  classical
  intro x hx y hy hxy
  apply (G.mem_neighborFinset x y).mp
  rw [neighbors G X d hsize hd x hx]
  exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxy.symm,(mem_vertices X y).mpr hy⟩)

theorem complete_boundary (X : Set V) (d : ℕ)
    (hsize : (vertices X).card+(boundary G X).card ≤ d+1)
    (hd : ∀ x ∈ X, d ≤ G.degree x) :
    ∀ x ∈ X, ∀ y ∈ boundary G X, G.Adj x y := by
  classical
  intro x hx y hy
  apply (G.mem_neighborFinset x y).mp
  rw [neighbors G X d hsize hd x hx]
  exact Finset.mem_union_right _ hy
end Paper.CliqueSaturatedBoundary
