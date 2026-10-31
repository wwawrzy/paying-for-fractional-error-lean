import Paper.Averaging.Tasks.ActualRoleTaskSum
import Paper.Owners.Construction.OwnerRoleGlobalPartMean
import Paper.Averaging.Tasks.FiniteAverage

/-! Exact runtime/global-outcome equality for the entire fractional task
sum. The program computes only its own bounded natural numerator. -/
namespace Paper.ActualRoleTaskMean
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B : ℕ) (ξ : ℝ) (c : V → Fin (B + 1)) (v : V) :
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
        OwnerRoleNumerator.denominator Δ k Q T s q =
      FiniteAverage.vector (fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
        OutcomeVector.tasks G D R L (OwnerVirtualFacts.high G D R L Δ)
          (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts
          (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ)) v := by
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  have hh := OwnerRoleGlobalPartMean.spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B q M c v
  dsimp only
  rw [hh]
  unfold FiniteAverage.vector
  congr 1
  apply Finset.sum_congr rfl
  intro ζ _
  exact (ActualRoleTaskSum.spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B ξ c ζ v).symm

end Paper.ActualRoleTaskMean
