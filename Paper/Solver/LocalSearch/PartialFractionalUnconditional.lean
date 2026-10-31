import Paper.Solver.LocalSearch.PartialFractionalCorrect
import Paper.Solver.LocalSearch.PartialFractionalBudget
import Paper.Owners.Construction.OwnerBoundaryDistribution

/-! Full physical partial fractional solver with its boundary law proved.
Public partition parameters are chosen uniformly before the graph. -/
namespace Paper.PartialFractionalUnconditional
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem parameters (L : ℕ) (hL : 1 ≤ L) (Δ t : ℕ) (ht : 0 < t) (a : ℕ) (ha : 1 ≤ a) :
    ∃ k b T : ℕ, ∃ hk : 0 < k, ∃ hQ : 0 < 2 ^ b,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        ∀ {idBits : ℕ} (C : BitCode V idBits) (D R : Finset V), R ⊆ covered G D →
        MinorDensity.Bound G (a : ℝ) → ∀ (B : ℕ) (c : V → Fin (B + 1)),
        (∀ v, 1 ≤ (c v).val) → ∀ ξ : ℝ, 0 < ξ →
        let s := T * (3 * k + 1) + k + 2
        let r := k + s
        let q := LocalSolverMath.denominator a ξ
        let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
        let y := fun v => (((PartialFractionalProgram.program C L Δ r k t (2 ^ b) T s a B q M hQ).run G
          (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
            PartialFractionalProgram.denominator Δ k (2 ^ b) T s q
        PartialOptimum.Feasible G R y ∧
          PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
            (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
              B * ((HeavyRepair.heavy G D R L).card + ((OwnerVirtualFacts.high G D R L Δ).card : ℝ) +
                (16 / (t : ℝ)) * (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)).card) := by
  have hh : 2 * (a : ℝ) + 1 < (2 * a + 2 : ℕ) := by push_cast; linarith
  obtain ⟨k, b, T, hk, hQ, hboundary⟩ := OwnerBoundaryDistribution.parameters
    (a : ℝ) (Nat.cast_nonneg a) L hL (2 * a + 2) hh Δ t ht
  refine ⟨k, b, T, hk, hQ, ?_⟩
  intro V _ _ G _ idBits C D R hcover hden B c hc ξ hξ
  let s := T * (3 * k + 1) + k + 2
  let r := k + s
  exact PartialFractionalCorrect.spec G C D R hcover L Δ r k hk t ht (2 ^ b) T s hQ
    (by dsimp only [r]; omega) (by dsimp only [s]; omega)
    a ha hden B c hc ξ hξ ((16 / (t : ℝ)) * (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)).card)
    (hboundary G hden D R)

end Paper.PartialFractionalUnconditional
