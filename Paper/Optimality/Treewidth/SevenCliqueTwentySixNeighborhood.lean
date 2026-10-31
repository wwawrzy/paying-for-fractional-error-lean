import Paper.Optimality.Treewidth.SevenCliqueEightNeighborhood
import Paper.Optimality.Treewidth.CliqueEightRegularFour
namespace Paper.SevenCliqueTwentySixNeighborhood
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem has_eight (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) (horder : Fintype.card V = 26) :
    ∃ C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent,
      (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8 := by
  classical
  obtain ⟨C,D,hCD,hdis,hno,hclC,hclD⟩ := SevenCliqueEightComponents.separated_pair G hG v hv hmin hcn hproper hsep
  let A := insert v (G.neighborFinset v)
  let X := vertices (outside G (insert v (G.neighborSet v)) C)
  let Y := vertices (outside G (insert v (G.neighborSet v)) D)
  have hX : 8 ≤ X.card := SevenCliqueEightComponent.component_eight G hG v hv hmin hcn C
  have hY : 8 ≤ Y.card := SevenCliqueEightComponent.component_eight G hG v hv hmin hcn D
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
  by_cases hx8 : X.card = 8
  · exact ⟨C,hx8⟩
  · have hy8 : Y.card = 8 := by omega
    exact ⟨D,hy8⟩

theorem no_four_clique (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) (horder : Fintype.card V = 26)
    (S : Finset V) (hS : S.card = 4) (hsub : S ⊆ G.neighborFinset v)
    (hcl : G.IsClique (S : Set V)) : False := by
  classical
  obtain ⟨C,hC⟩ := has_eight G hG v hv hmin hcn hproper hsep horder
  have hr := SevenCliqueEightNeighborhood.neighborhood_regular G hG v hv hmin hcn C hC
  let N := G.neighborFinset v
  let H := G.induce (N : Set V)
  have hN : Fintype.card (N : Set V) = 8 := by
    have hh := (G.card_neighborFinset_eq_degree v).trans hv
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hh
  have hreg : ∀ w : (N : Set V), H.degree w = 5 := by
    intro w
    rw [InducedCounting.degree_induce_eq_inducedDegree G N w]
    exact hr w.val w.property
  have hf : H.IsKMinorFree 6 := CliqueRootedProjection.excludes 7 (by decide) hG
    (SevenCliqueProjection.induced_model G (N : Set V)) v
    (by
      intro w hh
      have hw : w.val ∈ N := w.property
      have heq : w.val = v := (show v = w.val from hh).symm
      have hvN : v ∈ N := heq ▸ hw
      exact G.notMem_neighborFinset_self v hvN)
    (by intro w; exact ⟨w.val,rfl,(G.mem_neighborFinset v w.val).mp w.property⟩)
  let Q : Finset (N : Set V) := Finset.univ.filter (fun w => w.val ∈ S)
  have himage : Q.image Subtype.val = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hw).2
    · intro hz
      exact Finset.mem_image.mpr ⟨⟨z,hsub hz⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,rfl⟩
  have hQ : Q.card = 4 := by
    have hh := congrArg Finset.card himage
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hS] at hh
    exact hh
  have hQcl : H.IsClique (Q : Set (N : Set V)) := by
    intro x hx y hy hxy
    exact hcl ((Finset.mem_filter.mp hx).2) ((Finset.mem_filter.mp hy).2)
      (fun hh => hxy (Subtype.ext hh))
  exact hf (CliqueEightRegularFour.minor H Q hN hQ hreg hQcl)

end Paper.SevenCliqueTwentySixNeighborhood

