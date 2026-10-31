import Paper.Optimality.Treewidth.SevenCliqueEightBoundaryUpper
import Paper.Optimality.Treewidth.SevenCliqueEightComponents
namespace Paper.SevenCliqueEightExteriorSize
open SimpleGraph CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def vertices (X : Set V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => x ∈ X)
theorem mem_vertices (X : Set V) (x : V) : x ∈ vertices X ↔ x ∈ X := by
  classical
  simp [vertices]
theorem order_boundary (X : Set V) (hne : X.Nonempty) (d : ℕ)
    (hdeg : ∀ x ∈ X, d ≤ G.degree x) :
    d+1 ≤ (vertices X).card+(boundary G X).card := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hxF : x ∈ (vertices X) := (mem_vertices X x).mpr hx
  have hs : G.neighborFinset x ⊆ ((vertices X).erase x) ∪ boundary G X := by
    intro y hy
    have hxy := (G.mem_neighborFinset x y).mp hy
    by_cases hyX : y ∈ X
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxy.ne.symm,(mem_vertices X y).mpr hyX⟩)
    · exact Finset.mem_union_right _ ((mem_boundary G X y).mpr ⟨hyX,x,hx,hxy.symm⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree,Finset.card_erase_of_mem hxF] at hh
  have hp : 0 < (vertices X).card := Finset.card_pos.mpr ⟨x,hxF⟩
  have hd := hdeg x hx
  omega

theorem component_two (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    2 ≤ (vertices (outside G (insert v (G.neighborSet v)) C)).card := by
  classical
  let A : Set V := insert v (G.neighborSet v)
  let X := outside G A C
  have hne : X.Nonempty := by
    obtain ⟨x,hx⟩ := C.nonempty_supp
    exact ⟨x.val,x,hx,rfl⟩
  have hb := SevenCliqueEightBoundaryUpper.component_boundary_card G hG v hv hcn C
  have hh := order_boundary G X hne 8 (fun x _ => by have h := hmin x; omega)
  change 2 ≤ (vertices X).card
  change (boundary G X).card ≤ 7 at hb
  omega
theorem order_thirteen (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) :
    13 ≤ Fintype.card V := by
  classical
  obtain ⟨C,D,hCD,hdis,hno,hclC,hclD⟩ := SevenCliqueEightComponents.separated_pair G hG v hv hmin hcn hproper hsep
  let A := insert v (G.neighborFinset v)
  let X := vertices (outside G (insert v (G.neighborSet v)) C)
  let Y := vertices (outside G (insert v (G.neighborSet v)) D)
  have hX : 2 ≤ X.card := component_two G hG v hv hmin hcn C
  have hY : 2 ≤ Y.card := component_two G hG v hv hmin hcn D
  have hA : A.card = 9 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),G.card_neighborFinset_eq_degree,hv]
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzY
    exact Set.disjoint_left.mp hdis ((mem_vertices _ z).mp hzX) ((mem_vertices _ z).mp hzY)
  have hAXY : Disjoint A (X ∪ Y) := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzXY
    have hzClosed : z ∈ insert v (G.neighborSet v) := by
      simpa only [A,Finset.mem_insert,G.mem_neighborFinset,Set.mem_insert_iff,Set.mem_setOf_eq] using hzA
    rcases Finset.mem_union.mp hzXY with hzX | hzY
    · exact outside_subset G (insert v (G.neighborSet v)) C ((mem_vertices _ z).mp hzX) hzClosed
    · exact outside_subset G (insert v (G.neighborSet v)) D ((mem_vertices _ z).mp hzY) hzClosed
  have hh := Finset.card_le_card (Finset.subset_univ (A ∪ (X ∪ Y)))
  rw [Finset.card_union_of_disjoint hAXY,Finset.card_union_of_disjoint hXY,hA,Finset.card_univ] at hh
  omega
end Paper.SevenCliqueEightExteriorSize
#print axioms Paper.SevenCliqueEightExteriorSize.order_boundary
#print axioms Paper.SevenCliqueEightExteriorSize.component_two
#print axioms Paper.SevenCliqueEightExteriorSize.order_thirteen
