import Paper.Optimality.Treewidth.CliqueNoCrossCount
import Paper.Optimality.Treewidth.SevenCliqueEightExact
namespace Paper.SevenCliqueTwentyFiveCore
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem order_twenty_six (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (he : G.edgeFinset.card+14 = 5*Fintype.card V) :
    26 ≤ Fintype.card V := by
  classical
  have hlow := SevenCliqueEightComponent.order_twenty_five G hG v hv hmin hcn hproper hsep
  by_contra hn
  have horder : Fintype.card V = 25 := by omega
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

  have hx8 : X.card = 8 := by omega
  have hy8 : Y.card = 8 := by omega
  have hcover : A ∪ (X ∪ Y) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hAXY,Finset.card_union_of_disjoint hXY,hA,hx8,hy8,Finset.card_univ,horder]
  have hxE : G.inducedEdgeCount X = 22 := SevenCliqueEightExact.component_edges G hG v hv hmin hcn C hx8
  have hyE : G.inducedEdgeCount Y = 22 := SevenCliqueEightExact.component_edges G hG v hv hmin hcn D hy8
  have hnoXY : ∀ x ∈ X, ∀ y ∈ Y, ¬G.Adj x y := by
    intro x hx y hy
    exact hno x ((mem_vertices _ x).mp hx) y ((mem_vertices _ y).mp hy)
  have hE : G.inducedEdgeCount (X ∪ Y) = 44 := by
    rw [CliqueNoCrossCount.edges_union G X Y hXY hnoXY,hxE,hyE]
  have hbase : 28 ≤ G.inducedEdgeCount A := by
    have hb := SevenCliqueSixComponent.closed_base G v hv hcn
    have hs := InducedCounting.sum_inducedDegree_eq_two_mul G A
    change 56 ≤ ∑ x ∈ A, G.inducedDegree x A at hb
    omega
  have hcard : (X ∪ Y).card = 16 := by rw [Finset.card_union_of_disjoint hXY,hx8,hy8]
  have hd : 128 ≤ ∑ x ∈ X ∪ Y, G.inducedDegree x (A ∪ (X ∪ Y)) := by
    rw [hcover]
    simp_rw [CliqueNoCrossCount.degree_univ G]
    calc
      128 = ∑ _x ∈ X ∪ Y, (8 : ℕ) := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by have hh := hmin x; omega)
  rw [hcover] at hd
  have hb := CliqueRegionBalance.edge_balance G A (X ∪ Y) hAXY
  rw [hcover,CliqueNoCrossCount.edges_univ,hE] at hb
  omega

end Paper.SevenCliqueTwentyFiveCore
