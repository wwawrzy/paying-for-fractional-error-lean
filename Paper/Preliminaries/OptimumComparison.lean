import Paper.Certificates.Counting.PartialOptimum

/-! The true attained partial-cover optimum is at most every feasible cost. -/
namespace Paper.OptimumComparison
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem le_feasible (R : Finset V) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hx : PartialOptimum.Feasible G R x) : PartialOptimum.number G R c ≤ PartialOptimum.objective c x := by
  obtain ⟨z, hz, _, hmin⟩ := PartialOptimum.exists_optimum G R c hc
  have hleast : IsLeast (PartialOptimum.values G R c) (PartialOptimum.objective c z) := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact hmin y hy
  change sInf (PartialOptimum.values G R c) ≤ _
  rw [hleast.csInf_eq]
  exact hmin x hx
end Paper.OptimumComparison
