import Paper.Endpoints.Components.IntegralCoverOptimum

/-! A feasible output with universal cost comparison realizes the actual
integral optimum. Its own feasibility supplies the nonempty cost set. -/
namespace Paper.IntegralCoverOptimum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Universal optimality identifies the exact benchmark without an additional
nonempty-row hypothesis or an externally supplied optimum witness. -/
theorem cost_eq_optimum (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (D : Finset V) (hD : Feasible C R D)
    (hmin : ∀ O : Finset V, Feasible C R O → cost c D ≤ cost c O) :
    cost c D = optimum C R c := by
  apply Nat.le_antisymm _ (optimum_le_cost C R c hD)
  have hne : (values C R c).Nonempty := ⟨cost c D, D, hD, rfl⟩
  obtain ⟨O, hO, he⟩ := Nat.sInf_mem hne
  change cost c D ≤ sInf (values C R c)
  rw [← he]
  exact hmin O hO

end Paper.IntegralCoverOptimum

#print axioms Paper.IntegralCoverOptimum.cost_eq_optimum
