import Paper.Solver.LocalSearch.PartialFractionalUnconditional
import Paper.Averaging.Tasks.ActualRepairCount
import Paper.Averaging.Tasks.CompilerParameters

/-! Uniform public parameters give any requested relative fractional
accuracy for the actual physical program, from a genuine initializer bound. -/
namespace Paper.ActualFractionalAccuracy
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem reciprocal {η : ℝ} (hη : 0 < η) : ∃ t : ℕ, 0 < t ∧ 8 / (t : ℝ) ≤ η := by
  obtain ⟨t, ht⟩ := exists_nat_gt (max 1 (8 / η))
  have hpos : (0 : ℝ) < t := by linarith [le_max_left (1 : ℝ) (8 / η)]
  have hnat : 0 < t := by exact_mod_cast hpos
  have hmul : 8 < (t : ℝ) * η := (div_lt_iff₀ hη).mp ((le_max_right 1 (8 / η)).trans_lt ht)
  exact ⟨t, hnat, (div_le_iff₀ hpos).mpr (by nlinarith)⟩

set_option maxHeartbeats 1000000 in
theorem parameters (a : ℕ) (ha : 1 ≤ a) (B : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L Δ t k b T : ℕ, ∃ hk : 0 < k, ∃ hQ : 0 < 2 ^ b, ∃ ξ : ℝ, 0 < ξ ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        ∀ {idBits : ℕ} (C : BitCode V idBits) (D R : Finset V), R ⊆ covered G D →
        MinorDensity.Bound G (a : ℝ) → ∀ c : V → Fin (B + 1),
        (∀ v, 1 ≤ (c v).val) → ((D.card : ℝ) ≤ K * PartialOptimum.number G R (fun v => ((c v).val : ℝ))) →
        let s := T * (3 * k + 1) + k + 2
        let r := k + s
        let q := LocalSolverMath.denominator a ξ
        let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
        let y := fun v => (((PartialFractionalProgram.program C L Δ r k t (2 ^ b) T s a B q M hQ).run G
          (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
            PartialFractionalProgram.denominator Δ k (2 ^ b) T s q
        PartialOptimum.Feasible G R y ∧
          PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
            (1 + δ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  obtain ⟨L, Δ, ξ, η, hL, hΔ, hξ, hη, hparam⟩ :=
    CompilerParameters.exists_parameters a ha (B : ℝ) K (Nat.cast_nonneg B) hK hδ
  obtain ⟨t, ht, htrate⟩ := reciprocal hη
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hLNat : 1 ≤ L := by
    have hpos : (0 : ℝ) < L := by linarith
    have hnat : 0 < L := by exact_mod_cast hpos
    omega
  obtain ⟨k, b, T, hk, hQ, hrun⟩ := PartialFractionalUnconditional.parameters L hLNat Δ t ht a ha
  refine ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, ?_⟩
  intro V _ _ G _ idBits C D R hcover hden c hc hD
  obtain ⟨hy, hcost⟩ := hrun G C D R hcover hden B c hc ξ hξ
  refine ⟨hy, ?_⟩
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  have repair := @ActualRepairCount.bound V (inferInstance : Fintype V) (inferInstance : LinearOrder V)
  rw [hinst] at repair
  have hrepair := repair G D R hcover L Δ a ha hL hΔ hden t η hη htrate
  have hf : 0 ≤ OwnerCompilerBound.factor a L Δ η := by unfold OwnerCompilerBound.factor; positivity
  have hDcost := mul_le_mul_of_nonneg_left hD (mul_nonneg (Nat.cast_nonneg B) hf)
  have hcn : ∀ v, 0 ≤ ((c v).val : ℝ) := fun _ => Nat.cast_nonneg _
  obtain ⟨w, hw, he⟩ := PartialOptimum.exists_optimum_eq_number G R (fun v => ((c v).val : ℝ)) hcn
  have hτ : 0 ≤ PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
    rw [← he]
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (hcn v) (hw.1 v))
  calc
    _ ≤ (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
        B * (((HeavyRepair.heavy G D R L).card : ℝ) + (OwnerVirtualFacts.high G D R L Δ).card +
          (16 / (t : ℝ)) * (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)).card) := hcost
    _ ≤ (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
        B * OwnerCompilerBound.factor a L Δ η * D.card := by
      exact add_le_add le_rfl (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrepair (Nat.cast_nonneg B))
    _ ≤ (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
        (B * OwnerCompilerBound.factor a L Δ η) * (K * PartialOptimum.number G R (fun v => ((c v).val : ℝ))) :=
      add_le_add le_rfl hDcost
    _ = (1 + (ξ + B * K * OwnerCompilerBound.factor a L Δ η)) *
        PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl hparam) hτ

end Paper.ActualFractionalAccuracy
