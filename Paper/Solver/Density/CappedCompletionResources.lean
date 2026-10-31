import Paper.Solver.Density.CappedCompletion
import Paper.Solver.Density.CappedProtocolSchedules

/-! Resources of actual encoded execution up to each first local output.
The index denotes an observed prefix of one uniform repeated phase program.
It is not a public stopping horizon. Register and silent-halt refinements
are separate from this correspondence theorem. -/
namespace Paper.Density.CappedCompletionResources
open CappedCompletion
open CappedUniformParameters (rho)
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem schedule_observed (cap : ℚ) (m n : ℕ) :
    (CappedProtocolSchedules.schedule cap m (rho m) n).run G (fun _ => PUnit.unit) =
      observed G cap m n := CappedProtocolSchedules.schedule_run G cap m (rho m) n

theorem first_completion (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (v : V) :
    let n := firstTime G p cap hc hm v
    let P := CappedProtocolSchedules.schedule (V := V) cap m (rho m) n
    (P.run G (fun _ => PUnit.unit) v).done = true ∧
      P.rounds ≤ 5 + 6 * CappedGrowth.timeBound m Delta ∧
      P.maxBits G (fun _ => PUnit.unit) ≤ (2*m+5)*Nat.clog 2 (Fintype.card V+2) ∧
      ((P.run G (fun _ => PUnit.unit) v).output = true ↔ v ∈ output G p cap hc hm) := by
  dsimp only
  have hn := firstTime_le G p cap hc hm Delta hdegree v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [schedule_observed]
    exact firstTime_done G p cap hc hm v
  · rw [CappedProtocolSchedules.schedule_rounds]
    omega
  · simpa only [Nat.mul_zero, Nat.add_zero] using
      CappedProtocolSchedules.schedule_bits G cap m (rho m)
        (firstTime G p cap hc hm v) Delta 0 hdegree hD (by simpa using hn)
  · rw [schedule_observed]
    simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]

end Paper.Density.CappedCompletionResources
#print axioms Paper.Density.CappedCompletionResources.first_completion
