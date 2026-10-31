import Paper.Optimality.Treewidth.CliqueAffineSeparation
import Paper.Optimality.Treewidth.CliqueNeighborhoodExterior
namespace Paper.CliqueAffineBoundaryBudget
open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem separator_budget (k b B : ℕ)
    (he : G.edgeFinset.card+b=k*Fintype.card V) (hd : ∀ v, B ≤ G.degree v)
    (hminimal : CliqueMinorMinimal.BelowThreshold G k b B)
    (S : Finset V) (s : Separation G S) :
    (G.induce (S : Set V)).edgeFinset.card+b+2 ≤ k*S.card := by
  classical
  letI : Fintype s.left := Fintype.ofFinite _
  letI : Fintype s.right := Fintype.ofFinite _
  have hL := hminimal s.left (G.induce s.left) (IsMinor.of_induce G _)
    (CliqueAffineSeparation.left_floor G s B hd) (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_left_lt G s)
  have hRfloor : B ≤ Fintype.card s.right := by
    have hh := CliqueAffineSeparation.left_floor G (CliqueFourSeparation.flip G s) B hd
    simpa only [Fintype.card_eq_nat_card] using hh
  have hR := hminimal s.right (G.induce s.right) (IsMinor.of_induce G _) hRfloor (by
    simpa only [Nat.card_eq_fintype_card] using Separation.card_right_lt G s)
  have hsum := CliqueSeparationCount.edge_sum G s
  have hv := congrArg (fun n => k*n) (CliqueSeparationCount.vertex_sum G s)
  simp only [Nat.mul_add] at hv
  omega

theorem boundary_budget
    (he : G.edgeFinset.card+14=5*Fintype.card V) (hd : ∀ v, 5 ≤ G.degree v)
    (hminimal : CliqueMinorMinimal.BelowThreshold G 5 14 5)
    (v : V) (X : Set V) (hne : X.Nonempty)
    (hout : X ⊆ (insert v (G.neighborSet v))ᶜ) :
    (G.induce (boundary G X : Set V)).edgeFinset.card+16 ≤ 5*(boundary G X).card ∧
      4 ≤ (boundary G X).card := by
  classical
  have hv : v ∉ X := fun hh => hout hh (Set.mem_insert _ _)
  have hno : ∀ z ∈ X, ¬G.Adj v z := fun z hz hadj => hout hz (Or.inr hadj)
  have hh := separator_budget G 5 14 5 he hd hminimal (boundary G X) (separation G X hne v hv hno)
  exact ⟨by omega,by omega⟩
end Paper.CliqueAffineBoundaryBudget
#print axioms Paper.CliqueAffineBoundaryBudget.separator_budget
#print axioms Paper.CliqueAffineBoundaryBudget.boundary_budget
