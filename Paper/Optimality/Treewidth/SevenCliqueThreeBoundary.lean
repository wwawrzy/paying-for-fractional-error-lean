import Paper.Optimality.Treewidth.CliqueSaturatedBoundary
import Paper.Optimality.Treewidth.CliqueInducedLoss
import Paper.Optimality.Treewidth.CliqueTriangleApices
namespace Paper.SevenCliqueThreeBoundary
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 7) (N : Finset V) (hN : N.card = 8)
    (X : Set V) (hX : (vertices X).card = 3)
    (hd : ∀ x ∈ X, 8 ≤ G.degree x)
    (hbN : boundary G X ⊆ N) (hb : (boundary G X).card ≤ 6)
    (hlocal : ∀ b ∈ boundary G X, 5 ≤ G.inducedDegree b N) : False := by
  classical
  let B := boundary G X
  have hne : X.Nonempty := by
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < (vertices X).card by omega)
    exact ⟨x,(mem_vertices X x).mp hx⟩
  have hbound := order_boundary G X hne 8 hd
  have hB : B.card = 6 := by change 9 ≤ (vertices X).card+B.card at hbound; change B.card ≤ 6 at hb; omega
  have hsize : (vertices X).card+(boundary G X).card ≤ 8+1 := by omega
  have hcl := CliqueSaturatedBoundary.clique G X 8 hsize hd
  have ht := CliqueSaturatedBoundary.complete_boundary G X 8 hsize hd
  have hdis : Disjoint (vertices X) B := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzB
    exact ((mem_boundary G X z).mp hzB).1 ((mem_vertices X z).mp hzX)
  apply CliqueTriangleApices.impossible G hG (vertices X) B hX
    (Finset.card_pos.mp (by omega)) hdis
  · intro x hx y hy hxy
    exact hcl ((mem_vertices X x).mp hx) ((mem_vertices X y).mp hy) hxy
  · intro x hx b hb
    exact ht x ((mem_vertices X x).mp hx) b hb
  · intro b
    have hh := CliqueInducedLoss.bound G N B b.val
    have hdiff : (N \ B).card = 2 := by rw [Finset.card_sdiff_of_subset hbN,hN,hB]
    have hl := hlocal b.val b.property
    have hdB : 3 ≤ G.inducedDegree b.val B := by rw [hdiff] at hh; omega
    rw [InducedCounting.degree_induce_eq_inducedDegree G B b]
    exact hdB

theorem component_boundary_seven (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hX : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 3) :
    (boundary G (outside G (insert v (G.neighborSet v)) C)).card = 7 := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  have hb := SevenCliqueEightBoundaryUpper.component_boundary_card G hG v hv8 hcn C
  change (boundary G X).card ≤ 7 at hb
  change (boundary G X).card = 7
  by_contra hn
  have hb6 : (boundary G X).card ≤ 6 := by omega
  have hout := outside_subset G A C
  have hbN : boundary G X ⊆ G.neighborFinset v := by
    intro z hz
    have hzA := boundary_subset G A C hz
    rcases hzA with rfl | hzN
    · obtain ⟨_,w,hw,hvw⟩ := (mem_boundary G X z).mp hz
      exact False.elim (hout hw (Or.inr hvw))
    · exact (G.mem_neighborFinset v z).mpr hzN
  apply impossible G hG (G.neighborFinset v)
    ((G.card_neighborFinset_eq_degree v).trans hv8) X hX
    (fun z _ => by have hh := hmin z; omega) hbN hb6
  intro b hb
  have hf : (G.neighborFinset v).filter (G.Adj b) = (G.commonNeighbors v b).toFinset := by
    ext w
    simp only [Finset.mem_filter,G.mem_neighborFinset,Set.mem_toFinset,mem_commonNeighbors]
  change 5 ≤ ((G.neighborFinset v).filter (G.Adj b)).card
  rw [hf,Set.toFinset_card]
  exact hcn b ((G.mem_neighborFinset v b).mp (hbN hb))

end Paper.SevenCliqueThreeBoundary

