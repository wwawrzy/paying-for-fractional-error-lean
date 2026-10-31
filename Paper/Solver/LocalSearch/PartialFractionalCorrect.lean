import Paper.Solver.LocalSearch.PartialFractionalArithmetic
import Paper.Averaging.Tasks.PartialFractionalMeanModel
import Paper.Owners.Construction.OwnerRepairFlags
import Paper.Averaging.Tasks.ActualRoleTaskMean

/-! Full correctness of the literal natural-numerator physical program.
Only the boundary distribution bound remains a mathematical dependency
for its global approximation guarantee. -/
namespace Paper.PartialFractionalCorrect
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem exact_mean {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B : ℕ) (ξ : ℝ) (c : V → Fin (B + 1)) (v : V) :
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    (((PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
        PartialFractionalProgram.denominator Δ k Q T s q =
      ActualRoleMeanOutcome.vector G C D R L Δ r k hk t Q T s a B hQ ξ c v := by
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  have hq : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (LocalSolverMath.denominator_pos a ξ)
  dsimp only
  rw [PartialFractionalProgram.run_program, PartialFractionalArithmetic.value Δ k Q T s q hQ hq]
  change ((OwnerVirtualCorrect.learned G C D R L Δ v).metadata.heavy.toNat : ℝ) +
    (((OwnerVirtualCorrect.learned G C D R L Δ v).metadata.center &&
      (OwnerVirtualCorrect.learned G C D R L Δ v).high).toNat : ℝ) +
    (((OwnerBoundaryMean.program C L Δ k t Q T hQ).run G
      (fun u => (decide (u ∈ D), decide (u ∈ R))) v).val : ℝ) / OwnerBoundaryMean.denominator Δ k Q T +
    (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
      OwnerRoleNumerator.denominator Δ k Q T s q = _
  rw [OwnerRepairFlags.heavy G C D R L Δ v, OwnerRepairFlags.high G C D R hcover L Δ v,
    FiniteMeanLinear.indicator, FiniteMeanLinear.indicator,
    OwnerBoundaryMeanAll.correct G C D R hcover L Δ k hk t ht Q T hQ v,
    ActualRoleTaskMean.spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B ξ c v]
  exact (PartialFractionalMeanModel.decompose G C D R L Δ r k hk t Q T s a B hQ ξ c v).symm

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    (β : ℝ) (hboundary : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      ((BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
        (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
        (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts).card : ℝ)) ≤
      Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) * β) :
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    let y := fun v => (((PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
        PartialFractionalProgram.denominator Δ k Q T s q
    PartialOptimum.Feasible G R y ∧
      PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
        (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
          B * ((HeavyRepair.heavy G D R L).card + ((OwnerVirtualFacts.high G D R L Δ).card : ℝ) + β) := by
  dsimp only
  have he := funext (exact_mean G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B ξ c)
  rw [he]
  exact ActualRoleMeanOutcome.spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a ha hden B c hc ξ hξ β hboundary

end Paper.PartialFractionalCorrect
