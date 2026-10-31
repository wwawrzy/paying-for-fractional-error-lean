import Paper.Communication.GeneralInitBroadcast
import Paper.Solver.LocalSearch.PartialFractionalBudget
import Paper.Initialization.Pruning.InitializedProgram

/-! Actual general weighted partial solver: initialize from private demand
bits and feed the selected bits into the physical fractional program. -/
namespace Paper.GeneralFractionalProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open BroadcastModel
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    Program V (Bool × Fin (B + 1))
      (Fin (PartialFractionalProgram.bound L Δ k Q T s q M + 1)) :=
  InitializedProgram.program (GeneralInitBroadcast.program C A)
    (PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q)
    (st : V → Bool × Fin (B + 1)) :
    (program C A L Δ r k t Q T s a B q M hQ).run G st =
      (PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ).run G
        (fun u => (((GeneralInitBroadcast.program C A).run G (fun v => (st v).1) u, (st u).1), (st u).2)) := by
  exact InitializedProgram.run G (GeneralInitBroadcast.program C A)
    (PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ) st

theorem rounds {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s a B q M hQ).rounds =
      (2 * A) * (4 + 2 * (GeneralInitBroadcast.rank A)) +
        (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) a M) := by
  rw [program, InitializedProgram.rounds, GeneralInitBroadcast.rounds, PartialFractionalProgram.rounds]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s a B q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C A L Δ r k t Q T s a B q M hQ).maxBits ≤
      max (1 + (GeneralInitBroadcast.rank A) * (c + 1))
        (PartialFractionalBudget.constant L Δ r k Q T s a B q M c) * Nat.clog 2 (n + 2) := by
  have hi := GeneralInitBroadcast.logarithmic_bits C A n c hids
  have hp := PartialFractionalBudget.logarithmic_bits C L Δ r k t Q T s a B q M hQ n c hids
  rw [program, InitializedProgram.maxBits]
  calc
    _ ≤ max ((1 + (GeneralInitBroadcast.rank A) * (c + 1)) * Nat.clog 2 (n + 2))
      (PartialFractionalBudget.constant L Δ r k Q T s a B q M c * Nat.clog 2 (n + 2)) := max_le_max hi hp
    _ = _ := by rw [max_mul_mul_right]

end Paper.GeneralFractionalProgram
