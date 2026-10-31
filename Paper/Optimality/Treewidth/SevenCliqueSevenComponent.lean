import Paper.Optimality.Treewidth.CliqueRegionSeven
import Paper.Optimality.Treewidth.SevenCliqueSixComponent
namespace Paper.SevenCliqueSevenComponent
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component_seven (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    7 ≤ (vertices (outside G (insert v (G.neighborSet v)) C)).card := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let S := insert v (G.neighborFinset v)
  let T := vertices X
  have hSA : ∀ z, z ∈ S ↔ z ∈ A := by
    intro z
    simp only [S,A,Finset.mem_insert,G.mem_neighborFinset,Set.mem_insert_iff,Set.mem_setOf_eq]
    rfl
  have hout := outside_subset G A C
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro z hzS hzT
    exact hout ((mem_vertices X z).mp hzT) ((hSA z).mp hzS)
  have hS : S.card = 9 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),G.card_neighborFinset_eq_degree,hv8]
  have hT : T.Nonempty := by
    obtain ⟨x,hx⟩ := C.nonempty_supp
    exact ⟨x.val,(mem_vertices X x.val).mpr ⟨x,hx,rfl⟩⟩
  apply CliqueRegionSeven.seven_le G hG S T hdis hS hT (SevenCliqueSixComponent.closed_base G v hv8 hcn)
  intro x hx
  have hxX : x ∈ X := (mem_vertices X x).mp hx
  have he : (S ∪ T).filter (G.Adj x) = G.neighborFinset x := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_union,G.mem_neighborFinset]
    constructor
    · exact fun h => h.2
    · intro hxz
      refine ⟨?_,hxz⟩
      by_cases hzX : z ∈ X
      · exact Or.inr ((mem_vertices X z).mpr hzX)
      · exact Or.inl ((hSA z).mpr (outside_boundary G A C x hxX z hzX hxz))
  have hd : G.inducedDegree x (S ∪ T) = G.degree x := by
    change ((S ∪ T).filter (G.Adj x)).card = G.degree x
    rw [he,G.card_neighborFinset_eq_degree]
  rw [hd]
  have hh := hmin x
  omega
theorem order_twenty_three (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) :
    23 ≤ Fintype.card V := by
  classical
  obtain ⟨C,D,hCD,hdis,hno,hclC,hclD⟩ := SevenCliqueEightComponents.separated_pair G hG v hv hmin hcn hproper hsep
  let A := insert v (G.neighborFinset v)
  let X := vertices (outside G (insert v (G.neighborSet v)) C)
  let Y := vertices (outside G (insert v (G.neighborSet v)) D)
  have hX : 7 ≤ X.card := component_seven G hG v hv hmin hcn C
  have hY : 7 ≤ Y.card := component_seven G hG v hv hmin hcn D
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
end Paper.SevenCliqueSevenComponent
