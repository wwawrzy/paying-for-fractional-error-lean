import Paper.Optimality.Treewidth.CliqueRegionNineDegree
import Paper.Optimality.Treewidth.SevenCliqueNineExact
import Paper.Optimality.Treewidth.CliqueDegreeExcessCount
namespace Paper.SevenCliqueNineDegree
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component_bound (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ a w, G.Adj a w → 5 ≤ Fintype.card (G.commonNeighbors a w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 9) :
    ∀ x ∈ vertices (outside G (insert v (G.neighborSet v)) C), G.degree x ≤ 9 := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let S := insert v (G.neighborFinset v)
  let T := vertices X
  have hSA : ∀ z, z ∈ S ↔ z ∈ A := by
    intro z
    simp only [S,A,Finset.mem_insert,G.mem_neighborFinset,Set.mem_insert_iff]
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
  have heq : ∀ x ∈ T, G.inducedDegree x (S ∪ T) = G.degree x := by
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
    exact hd
  have hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T) := by
    intro x hx
    rw [heq x hx]
    have hh := hmin x
    omega
  have hbase : 28 ≤ G.inducedEdgeCount S := by
    have hh := SevenCliqueSixComponent.closed_base G v hv8 (hcn v)
    have hs := InducedCounting.sum_inducedDegree_eq_two_mul G S
    change 56 ≤ ∑ x ∈ S, G.inducedDegree x S at hh
    omega
  have hf := CliqueExteriorComplementConnected.free_nine G hG (fun z => by have hh := hmin z; omega) hcn v hsep C (by omega)
  have hr := CliqueRegionNineDegree.bound G hG S T hdis hS hsize hf hbase hdeg
  intro x hx
  rw [← heq x hx]
  exact hr x hx

theorem component_sum_bound (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ a w, G.Adj a w → 5 ≤ Fintype.card (G.commonNeighbors a w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 9) :
    (∑ x ∈ vertices (outside G (insert v (G.neighborSet v)) C), G.degree x) ≤ 73 := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let S := insert v (G.neighborFinset v)
  let T := vertices X
  have hSA : ∀ z, z ∈ S ↔ z ∈ A := by
    intro z
    simp only [S,A,Finset.mem_insert,G.mem_neighborFinset,Set.mem_insert_iff]
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
  have heq : ∀ x ∈ T, G.inducedDegree x (S ∪ T) = G.degree x := by
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
    exact hd
  have hdeg : ∀ x ∈ T, 8 ≤ G.inducedDegree x (S ∪ T) := by
    intro x hx
    rw [heq x hx]
    have hh := hmin x
    omega
  have hbase : 28 ≤ G.inducedEdgeCount S := by
    have hh := SevenCliqueSixComponent.closed_base G v hv8 (hcn v)
    have hs := InducedCounting.sum_inducedDegree_eq_two_mul G S
    change 56 ≤ ∑ x ∈ S, G.inducedDegree x S at hh
    omega
  have hf := CliqueExteriorComplementConnected.free_nine G hG (fun z => by have hh := hmin z; omega) hcn v hsep C (by omega)
  have hr := CliqueRegionNineDegree.sum_bound G hG S T hdis hS hsize hf hbase hdeg
  have hsum : (∑ x ∈ T, G.inducedDegree x (S ∪ T)) = ∑ x ∈ T, G.degree x :=
    Finset.sum_congr rfl (fun x hx => heq x hx)
  change (∑ x ∈ T, G.degree x) ≤ 73
  omega

open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component_high_count (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ a w, G.Adj a w → 5 ≤ Fintype.card (G.commonNeighbors a w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 9) :
    ((vertices (outside G (insert v (G.neighborSet v)) C)).filter (fun x => 9 ≤ G.degree x)).card ≤ 1 := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  have hT : T.card = 9 := hsize
  have hs := component_sum_bound G hG v hv8 hmin hcn hsep C hsize
  change (∑ x ∈ T, G.degree x) ≤ 73 at hs
  exact CliqueDegreeExcessCount.at_most_one T (fun x => G.degree x)
    (fun x _ => by change 8 ≤ G.degree x; have hh := hmin x; omega) (by change (∑ x ∈ T, G.degree x) ≤ 8*T.card+1; omega)
end Paper.SevenCliqueNineDegree
