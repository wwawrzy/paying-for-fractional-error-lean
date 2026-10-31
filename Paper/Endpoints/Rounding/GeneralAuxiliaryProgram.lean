import Paper.Communication.ZoneSolveProgram
import Paper.Solver.LocalSearch.GeneralFractionalAccuracy
import Paper.Endpoints.Rounding.AuxiliaryFromMasked

/-! The actual general auxiliary solver runs on the physical input graph:
three preprocessing bits, one mask bit, initialized fractional BC, and a
local zero guard. Only fixed natural parameters occur in program code. -/
namespace Paper.GeneralAuxiliaryProgram
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    Program V Unit (Fin (PartialFractionalProgram.bound L Δ k Q T s q M + 1) × ZoneProgram.Env d) :=
  ZoneSolveProgram.program d (GeneralFractionalProgram.program C A L Δ r k t Q T s A (d + 1) q M hQ) 0

variable [Fintype V]

theorem rounds {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C A d L Δ r k t Q T s q M hQ).rounds = 4 +
      ((2 * A) * (4 + 2 * (GeneralInitBroadcast.rank A)) +
        (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M)) := by
  rw [program, ZoneSolveProgram.rounds, GeneralFractionalProgram.rounds]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C A d L Δ r k t Q T s q M hQ).maxBits ≤
      (max (1 + (GeneralInitBroadcast.rank A) * (c + 1))
        (PartialFractionalBudget.constant L Δ r k Q T s A (d + 1) q M c) + 1) * Nat.clog 2 (n + 2) := by
  have hp := GeneralFractionalProgram.logarithmic_bits C A L Δ r k t Q T s A (d + 1) q M hQ n c hids
  rw [program, ZoneSolveProgram.maxBits]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  apply max_le <;> nlinarith

theorem environment (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ} (C : BitCode V b)
    (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (v : V) :
    ((program C A d L Δ r k t Q T s q M hQ).run G (fun _ => ()) v).2 = ZoneProgram.expected G d v := by
  rw [program, ZoneSolveProgram.run]

set_option maxHeartbeats 1000000 in
theorem parameters (A : ℕ) (hA : 1 ≤ A) (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L Δ t k b T : ℕ, ∃ hk : 0 < k, ∃ hQ : 0 < 2 ^ b, ∃ ξ : ℝ, 0 < ξ ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (A : ℝ) → ∀ {idBits : ℕ} (C : BitCode V idBits),
        let s := T * (3 * k + 1) + k + 2
        let r := k + s
        let q := LocalSolverMath.denominator A ξ
        let M := ⌈(q + 2 * (A : ℝ)) * (((d + 1 : ℕ) : ℝ) * k)⌉₊
        let y := fun v => ((((program C A d L Δ r k t (2 ^ b) T s q M hQ).run G
          (fun _ => ()) v).1).val : ℝ) /
            PartialFractionalProgram.denominator Δ k (2 ^ b) T s q
        feasible (WeightedBudget.auxiliary G d) y ∧
          cost (WeightedBudget.auxiliary G d) y ≤ (1 + δ) * WeightedBudget.auxiliaryNumber G d := by
  obtain ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, hrun⟩ := GeneralFractionalAccuracy.parameters A hA (d + 1) δ hδ
  refine ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, ?_⟩
  intro V _ _ G _ hden idBits C
  let Z := WeightedBudget.zone G d
  let c := fun v => (ZoneProgram.expected G d v).cost
  have hc : ∀ v, 1 ≤ (c v).val := fun v => ZoneProgram.weight_pos d _ _
  have h := hrun (MaskedTaskGraph.graph G Z) (MaskedTaskGraph.density G Z hden) C
    (WeightedBudget.initialDemands G d) c hc
  let s := T * (3 * k + 1) + k + 2
  let r := k + s
  let q := LocalSolverMath.denominator A ξ
  let M := ⌈(q + 2 * (A : ℝ)) * (((d + 1 : ℕ) : ℝ) * k)⌉₊
  let P := GeneralFractionalProgram.program C A L Δ r k t (2 ^ b) T s A (d + 1) q M hQ
  let z := fun v => ((P.run (MaskedTaskGraph.graph G Z)
    (fun u => (decide (u ∈ WeightedBudget.initialDemands G d), c u)) v).val : ℝ) /
      PartialFractionalProgram.denominator Δ k (2 ^ b) T s q
  have hs := AuxiliaryFromMasked.spec G d z h.1 δ h.2
  have he : (fun v => ((((program C A d L Δ r k t (2 ^ b) T s q M hQ).run G
      (fun _ => ()) v).1).val : ℝ) / PartialFractionalProgram.denominator Δ k (2 ^ b) T s q) =
      (fun v => if v ∈ WeightedBudget.zone G d then z v else 0) := by
    rw [program, ZoneSolveProgram.run]
    funext v
    by_cases hv : v ∈ WeightedBudget.zone G d
    · simp only [if_pos hv]
      rfl
    · simp only [if_neg hv, Fin.val_zero, Nat.cast_zero, zero_div]
  dsimp only
  rw [he]
  exact hs

end Paper.GeneralAuxiliaryProgram
