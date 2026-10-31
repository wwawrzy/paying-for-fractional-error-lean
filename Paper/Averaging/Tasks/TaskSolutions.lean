import Paper.Averaging.Tasks.TaskSolverMath

/-! Fix the actual bounded-search solution once for every task label.
This supplies a family, rather than an approximation-oracle assumption. -/
namespace Paper.TaskSolutions
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D)
variable (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
variable (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
variable (ξ : ℝ) (hξ : 0 < ξ)

noncomputable def multiplicity (I B : Finset (Low D Q)) :
    ↥(PhysicalTasks.vertices G D R L Q I : Set V) → ℕ :=
  Classical.choose (TaskSolverMath.solve G D R L Q I B I.card le_rfl a ha hden c hc B₀ hB₀ hcost ξ hξ)

noncomputable def vector (I B : Finset (Low D Q)) :
    ↥(PhysicalTasks.vertices G D R L Q I : Set V) → ℝ :=
  LocalFractional.vector (LocalSolverMath.denominator a ξ)
    (multiplicity G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ I B)

theorem spec (I B : Finset (Low D Q)) :
    let H := PhysicalTasks.vertices G D R L Q I
    let z := vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ I B
    PartialOptimum.Feasible (G.induce (H : Set V))
      (InducedSubsets.lift H (OwnerTasks.demands G D R L Q I B)) z ∧
      PartialOptimum.objective (fun v => c v.val) z ≤ (1 + ξ) * TaskOptimum.number G D R L Q I B c ∧
      ∀ v, (LocalSolverMath.denominator a ξ : ℝ) * z v =
        multiplicity G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ I B v := by
  have h := Classical.choose_spec (TaskSolverMath.solve G D R L Q I B I.card le_rfl a ha hden c hc B₀ hB₀ hcost ξ hξ)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
end Paper.TaskSolutions
