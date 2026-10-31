import Paper.Solver.LocalSearch.GeneralFractionalAccuracy
import Paper.Communication.EncodedProgram

/-! Weighted partial solver for arbitrary real minor-density bounds. A
rounded integer is used internally, preserving the requested LP accuracy.
Every public integer parameter is fixed before the graph and private input. -/
namespace Paper.GeneralFractionalBroadcast
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem density_mono {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a b : ℝ} (hden : MinorDensity.Bound G a) (hab : a ≤ b) :
    MinorDensity.Bound G b := by
  intro W _ _ J _ hm
  exact (hden W J hm).trans (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))

variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s B q M : ℕ) (hQ : 0 < Q) :
    Program V (Bool × Fin (B + 1)) (Fin (PartialFractionalProgram.bound L Δ k Q T s q M + 1)) :=
  GeneralFractionalProgram.program C A L Δ r k t Q T s A B q M hQ

variable [Fintype V]

theorem rounds {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s B q M : ℕ) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s B q M hQ).rounds =
      (2 * A) * (4 + 2 * GeneralInitBroadcast.rank A) +
        (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M) :=
  GeneralFractionalProgram.rounds C A L Δ r k t Q T s A B q M hQ

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s B q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C A L Δ r k t Q T s B q M hQ).maxBits ≤
      max (1 + GeneralInitBroadcast.rank A * (c + 1))
        (PartialFractionalBudget.constant L Δ r k Q T s A B q M c) * Nat.clog 2 (n + 2) :=
  GeneralFractionalProgram.logarithmic_bits C A L Δ r k t Q T s A B q M hQ n c hids

set_option maxHeartbeats 1000000 in
theorem parameters (a : ℝ) (ha : 1 ≤ a) (B : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ {idBits : ℕ} (C : BitCode V idBits) (R : Finset V)
          (c : V → Fin (B + 1)), (∀ v, 1 ≤ (c v).val) →
        let y := fun v => (((program C A L Δ r k t Q T s B q M hQ).runEncoded G
          (fun u => (decide (u ∈ R), c u)) v).val : ℝ) /
            PartialFractionalProgram.denominator Δ k Q T s q
        PartialOptimum.Feasible G R y ∧
          PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
            (1 + δ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  let A := ⌈a⌉₊
  have hA : 1 ≤ A := Nat.one_le_ceil_iff.mpr (by linarith)
  obtain ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, hrun⟩ := GeneralFractionalAccuracy.parameters A hA B δ hδ
  let s := T * (3 * k + 1) + k + 2
  let r := k + s
  let q := LocalSolverMath.denominator A ξ
  let M := ⌈(q + 2 * (A : ℝ)) * ((B : ℝ) * k)⌉₊
  have hq : 0 < q := by have h := LocalSolverMath.denominator_pos A ξ; omega
  refine ⟨A, L, Δ, r, k, t, 2 ^ b, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden idBits C R c hc
  have h := hrun G (density_mono G hden (Nat.le_ceil a)) C R c hc
  dsimp only
  rw [program, Program.runEncoded_eq_run]
  exact h

end Paper.GeneralFractionalBroadcast
