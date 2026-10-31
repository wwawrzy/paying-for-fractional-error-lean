import Paper.Averaging.Tasks.TaskBudget
import Paper.Solver.LocalSearch.LocalSolverMath
import Paper.Preliminaries.MinorInheritance

/-! Apply the actual bounded exact search to each actual physical task.
The search budget and denominator depend only on fixed parameters. Its
broadcast execution and physical diameter bound remain separate. -/
namespace Paper.TaskSolverMath
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem solve (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    (k : ℕ) (hI : I.card ≤ k) (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
    (ξ : ℝ) (hξ : 0 < ξ) :
    let H := PhysicalTasks.vertices G D R L Q I
    let T := InducedSubsets.lift H (OwnerTasks.demands G D R L Q I B)
    let q := LocalSolverMath.denominator a ξ
    ∃ p : ↥(H : Set V) → ℕ,
      LocalFractional.best (G.induce (H : Set V)) (a : ℝ) (fun v => c v.val)
        ⌈(q + 2 * (a : ℝ)) * (B₀ * k)⌉₊ (LocalFractional.demand T q) = some p ∧
      PartialOptimum.Feasible (G.induce (H : Set V)) T (LocalFractional.vector q p) ∧
      PartialOptimum.objective (fun v => c v.val) (LocalFractional.vector q p) ≤
        (1 + ξ) * TaskOptimum.number G D R L Q I B c ∧
      ∀ v, (q : ℝ) * LocalFractional.vector q p v = p v := by
  classical
  dsimp only
  let H := PhysicalTasks.vertices G D R L Q I
  let T := InducedSubsets.lift H (OwnerTasks.demands G D R L Q I B)
  have hcn : ∀ v, 0 ≤ c v := fun v => zero_le_one.trans (hc v)
  have hbudget := (TaskBudget.optimum_bound G D R L Q I B c hcn B₀ hcost).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hI) hB₀)
  have hlocal := MinorDensity.induced_bound _ (MinorInheritance.induced G hden H)
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨p, hbest, hnonneg, hcover, hpcost, hq⟩ := LocalSolverMath.local_solver
    (G.induce (H : Set V)) T (a : ℝ) haR hlocal a ha le_rfl (fun v => c v.val)
    (fun v => hc v.val) (B₀ * k) ξ hξ hbudget
  exact ⟨p, hbest, ⟨hnonneg, hcover⟩, hpcost, hq⟩
end Paper.TaskSolverMath
