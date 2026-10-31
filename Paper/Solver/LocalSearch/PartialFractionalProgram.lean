import Paper.Owners.Construction.OwnerRoleNumerator
import Paper.Owners.Construction.OwnerBoundaryMean

/-! Concrete physical BC partial fractional solver: compute own repair
flags, exact boundary mean and exact task mean, then combine their bounded
natural numerators over a fixed public common denominator. -/
namespace Paper.PartialFractionalProgram
open BroadcastModel
variable {V : Type} [LinearOrder V]

def denominator (Δ k Q T s q : ℕ) : ℕ :=
  OwnerRoleNumerator.denominator Δ k Q T s q * OwnerBoundaryMean.denominator Δ k Q T

def bound (L Δ k Q T s q M : ℕ) : ℕ :=
  3 * denominator Δ k Q T s q +
    (OwnerRoleInputs.capacity L Δ k Q T s * M) * OwnerBoundaryMean.denominator Δ k Q T

def repairs (env : OwnerVirtualPrepare.Env V) : ℕ :=
  env.metadata.heavy.toNat + (env.metadata.center && env.high).toNat

theorem repairs_le (env : OwnerVirtualPrepare.Env V) : repairs env ≤ 2 := by
  unfold repairs
  cases env.metadata.heavy <;> cases env.metadata.center && env.high <;> decide

def numerator (Δ k Q T s q : ℕ) (env : OwnerVirtualPrepare.Env V) (pn tn : ℕ) : ℕ :=
  repairs env * denominator Δ k Q T s q + pn * OwnerRoleNumerator.denominator Δ k Q T s q +
    tn * OwnerBoundaryMean.denominator Δ k Q T

theorem numerator_le (L Δ k Q T s q M : ℕ) (env : OwnerVirtualPrepare.Env V)
    (pn tn : ℕ) (hp : pn ≤ OwnerBoundaryMean.denominator Δ k Q T)
    (ht : tn ≤ OwnerRoleInputs.capacity L Δ k Q T s * M) :
    numerator Δ k Q T s q env pn tn ≤ bound L Δ k Q T s q M := by
  have hr := Nat.mul_le_mul_right (denominator Δ k Q T s q) (repairs_le env)
  have hpn := Nat.mul_le_mul_right (OwnerRoleNumerator.denominator Δ k Q T s q) hp
  have htn := Nat.mul_le_mul_right (OwnerBoundaryMean.denominator Δ k Q T) ht
  dsimp only [numerator, bound, denominator] at *
  nlinarith

def finish (L Δ k Q T s q M : ℕ) :
    Program V (Fin (OwnerRoleInputs.capacity L Δ k Q T s * M + 1) ×
      (Fin (OwnerBoundaryMean.denominator Δ k Q T + 1) × OwnerVirtualPrepare.Env V))
      (Fin (bound L Δ k Q T s q M + 1)) :=
  .local fun _ _ st => ⟨numerator Δ k Q T s q st.2.2 st.2.1.val st.1.val,
    Nat.lt_succ_of_le (numerator_le L Δ k Q T s q M st.2.2 st.2.1.val st.1.val
      (Nat.le_of_lt_succ st.2.1.isLt) (Nat.le_of_lt_succ st.1.isLt))⟩

def program {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    Program V ((Bool × Bool) × Fin (B + 1)) (Fin (bound L Δ k Q T s q M + 1)) :=
  .seq (.local fun _ _ st => (st.1, st))
    (.seq (ProgramMemory.carry (OwnerVirtualPrepare.program C L Δ))
      (.seq (.local fun _ _ st => (st.2.1, (st.1, st.2)))
        (.seq (ProgramMemory.carry (OwnerBoundaryMean.program C L Δ k t Q T hQ))
          (.seq (.local fun _ _ st => (st.2.2, (st.1, st.2.1)))
            (.seq (ProgramMemory.carry (OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ))
              (finish L Δ k Q T s q M))))))

theorem denominator_pos (Δ k Q T s q : ℕ) (hQ : 0 < Q) (hq : 0 < q) :
    0 < denominator Δ k Q T s q :=
  Nat.mul_pos (OwnerRoleNumerator.denominator_pos Δ k Q T s q hQ hq)
    (OwnerBoundaryMean.denominator_pos Δ k Q T hQ)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q)
    (st : V → (Bool × Bool) × Fin (B + 1)) (v : V) :
    ((program C L Δ r k t Q T s a B q M hQ).run G st v).val =
      numerator Δ k Q T s q ((OwnerVirtualPrepare.program C L Δ).run G (fun u => (st u).1) v)
        (((OwnerBoundaryMean.program C L Δ k t Q T hQ).run G (fun u => (st u).1) v).val)
        (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G st v).val) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (OwnerVirtualPrepare.program C L Δ)]
  dsimp only
  rw [ProgramMemory.run G (OwnerBoundaryMean.program C L Δ k t Q T hQ)]
  dsimp only
  rw [ProgramMemory.run G (OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ)]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).rounds =
      34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) a M := by
  simp only [program, finish, Program.rounds, ProgramMemory.rounds, OwnerVirtualPrepare.rounds,
    OwnerBoundaryMean.rounds, OwnerRoleNumerator.rounds]
  omega

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).maxBits =
      max (OwnerVirtualPrepare.program C L Δ).maxBits
        (max (OwnerBoundaryMean.program C L Δ k t Q T hQ).maxBits
          (OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).maxBits) := by
  simp only [program, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]

end Paper.PartialFractionalProgram
