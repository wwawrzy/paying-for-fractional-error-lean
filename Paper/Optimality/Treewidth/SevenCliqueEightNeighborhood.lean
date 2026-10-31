import Paper.Optimality.Treewidth.CliqueRegionEight
import Paper.Optimality.Treewidth.CliqueClosedEdgeCount
import Paper.Optimality.Treewidth.SevenCliqueEightComponent
import Paper.Optimality.Treewidth.SevenCliqueSixComponent
namespace Paper.SevenCliqueEightNeighborhood
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem closed_edges (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    G.inducedEdgeCount (insert v (G.neighborFinset v)) = 28 := by
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
  have hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T) := by
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
  have hbase : 28 ≤ G.inducedEdgeCount S := by
    have hh := SevenCliqueSixComponent.closed_base G v hv8 hcn
    have hs := InducedCounting.sum_inducedDegree_eq_two_mul G S
    change 56 ≤ ∑ x ∈ S, G.inducedDegree x S at hh
    omega
  have hf := SevenCliqueEightComponent.small_component_free G hG v hv8 hmin C (by omega)
  exact (CliqueRegionEight.exact_counts G hG S T hdis hS hsize hf hbase hdeg).2

theorem neighborhood_regular (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    ∀ w ∈ G.neighborFinset v, G.inducedDegree w (G.neighborFinset v) = 5 := by
  classical
  let N := G.neighborFinset v
  have hc := closed_edges G hG v hv8 hmin hcn C hsize
  have hid := CliqueClosedEdgeCount.identity G v
  have he : G.inducedEdgeCount N = 20 := by
    change G.inducedEdgeCount (insert v (G.neighborFinset v)) = G.inducedEdgeCount N+G.degree v at hid
    rw [hc,hv8] at hid
    omega
  have hN : N.card = 8 := (G.card_neighborFinset_eq_degree v).trans hv8
  have hlow : ∀ w ∈ N, 5 ≤ G.inducedDegree w N := by
    intro w hw
    have hf : N.filter (G.Adj w) = (G.commonNeighbors v w).toFinset := by
      ext z
      simp only [Finset.mem_filter,N,G.mem_neighborFinset,Set.mem_toFinset,mem_commonNeighbors]
    change 5 ≤ (N.filter (G.Adj w)).card
    rw [hf,Set.toFinset_card]
    exact hcn w ((G.mem_neighborFinset v w).mp hw)
  have hs := InducedCounting.sum_inducedDegree_eq_two_mul G N
  intro w hw
  change w ∈ N at hw
  have hrest : 35 ≤ ∑ z ∈ N.erase w, G.inducedDegree z N := by
    calc
      35 = ∑ _z ∈ N.erase w, (5 : ℕ) := by simp [Finset.card_erase_of_mem hw,hN]
      _ ≤ _ := Finset.sum_le_sum (fun z hz => hlow z (Finset.mem_erase.mp hz).2)
  have hsum := Finset.sum_erase_add N (fun z => G.inducedDegree z N) hw
  change (∑ z ∈ N.erase w, G.inducedDegree z N)+G.inducedDegree w N =
    ∑ z ∈ N, G.inducedDegree z N at hsum
  have hd := hlow w hw
  change G.inducedDegree w N = 5
  omega

end Paper.SevenCliqueEightNeighborhood

