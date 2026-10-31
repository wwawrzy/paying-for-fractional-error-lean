import Paper.Solver.LocalSearch.ActualFractionalAccuracy
import Paper.Solver.LocalSearch.GeneralFractionalProgram

/-! Uniform initialized weighted partial fractional BC solver for every
fixed integer minor-density bound. Public parameters precede the graph. -/
namespace Paper.GeneralFractionalAccuracy
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem initializer {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : ℕ) (hA : 1 ≤ A) (hden : MinorDensity.Bound G (A : ℝ))
    {idBits B : ℕ} (C : BitCode V idBits) (R : Finset V)
    (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val) :
    R ⊆ covered G (GeneralInitBroadcast.output G C A R) ∧
      ((GeneralInitBroadcast.output G C A R).card : ℝ) ≤
        GeneralInitBroadcast.constant A * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  obtain ⟨w, hw, he⟩ := PartialOptimum.exists_optimum_eq_number G R
    (fun v => ((c v).val : ℝ)) (fun _ => Nat.cast_nonneg _)
  have h := GeneralInitBroadcast.spec G C A hA hden R (fun v => ((c v).val : ℝ)) w
    (fun v => by change (1 : ℝ) ≤ ((c v).val : ℝ); exact_mod_cast hc v) hw.1 hw.2
  change R ⊆ covered G (GeneralInitBroadcast.output G C A R) ∧
    ((GeneralInitBroadcast.output G C A R).card : ℝ) ≤
      GeneralInitBroadcast.constant A * PartialOptimum.objective (fun v => ((c v).val : ℝ)) w at h
  rwa [he] at h

set_option maxHeartbeats 1000000 in
theorem parameters (A : ℕ) (hA : 1 ≤ A) (B : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L Δ t k b T : ℕ, ∃ hk : 0 < k, ∃ hQ : 0 < 2 ^ b, ∃ ξ : ℝ, 0 < ξ ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (A : ℝ) → ∀ {idBits : ℕ} (C : BitCode V idBits) (R : Finset V)
          (c : V → Fin (B + 1)), (∀ v, 1 ≤ (c v).val) →
        let s := T * (3 * k + 1) + k + 2
        let r := k + s
        let q := LocalSolverMath.denominator A ξ
        let M := ⌈(q + 2 * (A : ℝ)) * ((B : ℝ) * k)⌉₊
        let y := fun v => (((GeneralFractionalProgram.program C A L Δ r k t (2 ^ b) T s A B q M hQ).run G
          (fun u => (decide (u ∈ R), c u)) v).val : ℝ) /
            PartialFractionalProgram.denominator Δ k (2 ^ b) T s q
        PartialOptimum.Feasible G R y ∧
          PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
            (1 + δ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  obtain ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, hrun⟩ :=
    ActualFractionalAccuracy.parameters A hA B (GeneralInitBroadcast.constant A)
      (GeneralInitBroadcast.constant_nonneg A) δ hδ
  refine ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, ?_⟩
  intro V _ _ G _ hden idBits C R c hc
  obtain ⟨hcover, hsize⟩ := initializer G A hA hden C R c hc
  have h := hrun G C (GeneralInitBroadcast.output G C A R) R hcover hden c hc hsize
  dsimp only
  rw [GeneralFractionalProgram.run_program]
  have he : (fun u => (((GeneralInitBroadcast.program C A).run G (fun v => decide (v ∈ R)) u,
        decide (u ∈ R)), c u)) =
      (fun u => ((decide (u ∈ GeneralInitBroadcast.output G C A R), decide (u ∈ R)), c u)) := by
    funext u
    simp only [GeneralInitBroadcast.output, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.decide_eq_true]
  rw [he]
  exact h

end Paper.GeneralFractionalAccuracy
