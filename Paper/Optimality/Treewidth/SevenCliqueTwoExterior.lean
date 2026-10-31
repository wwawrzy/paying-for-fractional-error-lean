import Paper.Optimality.Treewidth.CliquePairedApices
import Paper.Optimality.Treewidth.CliqueTwoDeletion
import Paper.Optimality.Treewidth.CliqueTwoVertexEdge
namespace Paper.SevenCliqueTwoExterior
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (x y : V) (hxyne : x ≠ y)
    (hout : ({x,y} : Set V) ⊆ (insert v (G.neighborSet v))ᶜ)
    (hbN : boundary G ({x,y} : Set V) ⊆ G.neighborFinset v)
    (hb : (boundary G ({x,y} : Set V)).card ≤ 7) : False := by
  classical
  let X : Set V := {x,y}
  let B := boundary G X
  let N := G.neighborFinset v
  have hX : (vertices X).card = 2 := by
    have he : vertices X = {x,y} := by ext z; simp [mem_vertices,X]
    rw [he,Finset.card_pair hxyne]
  have hB : B.card = 7 := CliqueTwoVertexBoundary.boundary_seven G X hX hb (fun z _ => hmin z)
  have hcomplete := CliqueTwoVertexBoundary.complete_boundary G X hX hb (fun z _ => hmin z)
  have hN : N.card = 8 := (G.card_neighborFinset_eq_degree v).trans hv8
  obtain ⟨c,hcN,hcB⟩ : ∃ c ∈ N, c ∉ B := by
    by_contra hn
    push Not at hn
    have hh := Finset.card_le_card (show N ⊆ B from hn)
    omega
  have hBeq : B = N.erase c := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; exact Finset.mem_erase.mpr ⟨fun he => hcB (he ▸ hz),hbN hz⟩
    · rw [Finset.card_erase_of_mem hcN,hN,hB]
  obtain ⟨a,haB⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have haN := hbN haB
  have hac : a ≠ c := fun hh => hcB (hh ▸ haB)
  let T := (N.erase a).erase c
  have hTcard : T.card = 6 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac.symm,hcN⟩),
      Finset.card_erase_of_mem haN,hN]
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTN : T ⊆ N := fun z hz => (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  have hTB : T ⊆ B := by
    intro z hz
    rw [hBeq]
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hTN hz⟩
  have hxout := hout (show x ∈ ({x,y} : Set V) by simp)
  have hyout := hout (show y ∈ ({x,y} : Set V) by simp)
  have hxN : x ∉ N := fun hh => hxout (Or.inr ((G.mem_neighborFinset v x).mp hh))
  have hyN : y ∉ N := fun hh => hyout (Or.inr ((G.mem_neighborFinset v y).mp hh))
  have hva : G.Adj v a := (G.mem_neighborFinset v a).mp haN
  apply CliquePairedApices.impossible G hG T hTne x y v a
    (CliqueTwoVertexEdge.adjacent G x y hb (hmin x)) hva
    (hcomplete x (by simp [X]) a haB) (hcomplete y (by simp [X]) a haB)
    (fun hh => hxout (Or.inl hh)) (fun hh => hyout (Or.inl hh))
    (fun hh => hxN (hTN hh)) (fun hh => hyN (hTN hh))
    (fun hh => G.notMem_neighborFinset_self v (hTN hh))
    (fun hh => (Finset.mem_erase.mp (Finset.mem_erase.mp hh).2).1 rfl)
    (fun z hz => hcomplete x (by simp [X]) z (hTB hz))
    (fun z hz => hcomplete y (by simp [X]) z (hTB hz))
    (fun z hz => (G.mem_neighborFinset v z).mp (hTN hz))
  intro z
  have hzN := hTN z.property
  have hf : N.filter (G.Adj z.val) = (G.commonNeighbors v z.val).toFinset := by
    ext w
    simp only [Finset.mem_filter,N,G.mem_neighborFinset,Set.mem_toFinset,mem_commonNeighbors]
  have hdN : 5 ≤ G.inducedDegree z.val N := by
    change 5 ≤ (N.filter (G.Adj z.val)).card
    rw [hf,Set.toFinset_card]
    exact hcn z.val ((G.mem_neighborFinset v z.val).mp hzN)
  have hdT := CliqueTwoDeletion.induced_degree G N a c z.val hdN
  have heT := InducedCounting.degree_induce_eq_inducedDegree G T z
  rw [heT]
  exact hdT

/-- Every actual exterior component has at least three vertices. -/
theorem component_three (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    3 ≤ (vertices (outside G (insert v (G.neighborSet v)) C)).card := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  have htwo := SevenCliqueEightExteriorSize.component_two G hG v hv8 hmin hcn C
  change 3 ≤ (vertices X).card
  change 2 ≤ (vertices X).card at htwo
  by_contra hn
  have hecard : (vertices X).card = 2 := by omega
  obtain ⟨x,y,hxy,he⟩ := Finset.card_eq_two.mp hecard
  have hXeq : X = ({x,y} : Set V) := by
    ext z
    rw [← mem_vertices X z,he]
    simp
  have hout := outside_subset G A C
  have hb := SevenCliqueEightBoundaryUpper.component_boundary_card G hG v hv8 hcn C
  have hbN : boundary G X ⊆ G.neighborFinset v := by
    intro z hz
    have hzA := boundary_subset G A C hz
    rcases hzA with rfl | hzN
    · obtain ⟨_,w,hw,hvw⟩ := (mem_boundary G X z).mp hz
      exact False.elim (hout hw (Or.inr hvw))
    · exact (G.mem_neighborFinset v z).mpr hzN
  apply impossible G hG v hv8 (fun z => by have hh := hmin z; omega) hcn x y hxy
  · rw [← hXeq]; exact hout
  · rw [← hXeq]; exact hbN
  · rw [← hXeq]; exact hb

theorem order_fifteen (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) :
    15 ≤ Fintype.card V := by
  classical
  obtain ⟨C,D,hCD,hdis,hno,hclC,hclD⟩ := SevenCliqueEightComponents.separated_pair G hG v hv hmin hcn hproper hsep
  let A := insert v (G.neighborFinset v)
  let X := vertices (outside G (insert v (G.neighborSet v)) C)
  let Y := vertices (outside G (insert v (G.neighborSet v)) D)
  have hX : 3 ≤ X.card := component_three G hG v hv hmin hcn C
  have hY : 3 ≤ Y.card := component_three G hG v hv hmin hcn D
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
end Paper.SevenCliqueTwoExterior


