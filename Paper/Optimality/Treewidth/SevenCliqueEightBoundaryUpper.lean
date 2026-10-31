import Paper.Optimality.Treewidth.CliqueEightMinFive
import Paper.Optimality.Treewidth.CliqueMissingEdgeCompletion
import Paper.Optimality.Treewidth.CliqueInducedLift
namespace Paper.SevenCliqueEightBoundaryUpper
open SimpleGraph CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem missing_neighbor (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (X : Set V) (hX : (G.induce X).Connected)
    (hout : X ⊆ (insert v (G.neighborSet v))ᶜ) :
    ∃ u ∈ G.neighborFinset v, u ∉ boundary G X := by
  classical
  have hn : Fintype.card (G.neighborSet v) = 8 := by rw [G.card_neighborSet_eq_degree,hv]
  have hd : ∀ w : G.neighborSet v, 5 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 5 w (hcn w w.property)
  obtain ⟨p,q,hpq,⟨m⟩⟩ := CliqueEightMinFive.minor (G.induce (G.neighborSet v)) hn hd
  let n := CliqueInducedLift.model G (G.neighborSet v) m
  have hsub : ∀ i, n.branchSet i ⊆ G.neighborSet v := CliqueInducedLift.branch_subset G _ m
  have havoid : ∀ i, v ∉ n.branchSet i := by
    intro i hi
    exact G.irrefl (hsub i hi)
  have htouch : ∀ i, ∃ z ∈ n.branchSet i, G.Adj v z := by
    intro i
    obtain ⟨z,hz⟩ := n.nonempty i
    exact ⟨z,hz,hsub i hz⟩
  have hdisj : ∀ i, Disjoint X (n.branchSet i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro z hzX hzB
    exact hout hzX (Or.inr (hsub i hzB))
  by_contra hnot
  push Not at hnot
  have hbound : ∀ z ∈ G.neighborSet v, z ∈ boundary G X := by
    intro z hz
    exact hnot z ((G.mem_neighborFinset v z).mpr hz)
  obtain ⟨a,ha⟩ := n.nonempty p
  obtain ⟨b,hb⟩ := n.nonempty q
  obtain ⟨_,z,hz,haz⟩ := (mem_boundary G X a).mp (hbound a (hsub p ha))
  obtain ⟨_,w,hw,hbw⟩ := (mem_boundary G X b).mp (hbound b (hsub q hb))
  exact CliqueMissingEdgeCompletion.rooted_impossible hG n X hX hdisj
    ⟨a,ha,z,hz,haz⟩ ⟨w,hw,b,hb,hbw.symm⟩ v
    (fun hh => hout hh (Set.mem_insert _ _)) havoid htouch

theorem component_boundary_card (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    (boundary G (outside G (insert v (G.neighborSet v)) C)).card ≤ 7 := by
  classical
  let A : Set V := insert v (G.neighborSet v)
  let X := outside G A C
  have hout := outside_subset G A C
  obtain ⟨u,hu,hmiss⟩ := missing_neighbor G hG v hv hcn X (outside_connected G A C) hout
  have hb : boundary G X ⊆ G.neighborFinset v := by
    intro z hz
    have hzA := boundary_subset G A C hz
    rcases hzA with rfl | hzN
    · obtain ⟨_,w,hw,hvw⟩ := (mem_boundary G X z).mp hz
      exact False.elim (hout hw (Or.inr hvw))
    · exact (G.mem_neighborFinset v z).mpr hzN
  have hs : boundary G X ⊆ (G.neighborFinset v).erase u := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun he => hmiss (he ▸ hz),hb hz⟩
  have hh := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem hu,G.card_neighborFinset_eq_degree,hv] at hh
  exact hh
end Paper.SevenCliqueEightBoundaryUpper
#print axioms Paper.SevenCliqueEightBoundaryUpper.missing_neighbor
#print axioms Paper.SevenCliqueEightBoundaryUpper.component_boundary_card
