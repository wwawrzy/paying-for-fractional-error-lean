import Paper.Communication.SurfaceFinalProgram
namespace Paper.SurfaceFinalProgram
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
def messageConstant (a K A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max (CurrentCriticalProgram.messageConstant 6 A L Δ r k Q T s q M c)
    (SmallComponentProgram.messageConstant a 1 K c)
theorem logarithmic_bits {b : ℕ} (ids : BitCode V b)
    (a K A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program 6 (PartialFractionalProgram.denominator Δ k Q T s q) a K ids
      (GeneralFractionalBroadcast.program ids A L Δ r k t Q T s 7 q M hQ)).maxBits ≤
      messageConstant a K A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  rw [total_maxBits]
  have hp := CurrentCriticalProgram.logarithmic_bits ids 6 A L Δ r k t Q T s q M hQ n c hids
  rw [CurrentCriticalProgram.maxBits] at hp
  have hs := SmallComponentProgram.logarithmic_bits ids a 1 K (by omega) n c hids
  have hpc := Nat.mul_le_mul_right (Nat.clog 2 (n + 2))
    (le_max_left (CurrentCriticalProgram.messageConstant 6 A L Δ r k Q T s q M c)
      (SmallComponentProgram.messageConstant a 1 K c))
  have hsc := Nat.mul_le_mul_right (Nat.clog 2 (n + 2))
    (le_max_right (CurrentCriticalProgram.messageConstant 6 A L Δ r k Q T s q M c)
      (SmallComponentProgram.messageConstant a 1 K c))
  exact max_le ((le_max_left _ _).trans (hp.trans hpc))
    (max_le ((le_max_right _ _).trans (hp.trans hpc)) (hs.trans hsc))
def portProgram {N b : ℕ} (d D a K : ℕ) (ids : BitCode V b)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    PortBroadcastModel.Program V Unit Bool :=
  KT0Compiler.program ids (program d D a K ids P)

theorem port_correct {N b : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (d D a K : ℕ) (ids : BitCode V b)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) (ports : PortBroadcastModel.Numbering G) :
    (portProgram d D a K ids P).runEncoded G ports (fun _ => ()) =
      (program d D a K ids P).runEncoded G (fun _ => ()) := by
  exact KT0Compiler.program_encoded_correct G ids _ ports _

theorem port_rounds {N b : ℕ} (d D a K : ℕ) (ids : BitCode V b)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (portProgram d D a K ids P).rounds = P.rounds + 11 + SmallComponentProgram.roundBound a K := by
  rw [portProgram, KT0Compiler.program_rounds, total_rounds, SmallComponentProgram.rounds]
  omega

theorem port_logarithmic_bits {b : ℕ} (ids : BitCode V b)
    (a K A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (portProgram 6 (PartialFractionalProgram.denominator Δ k Q T s q) a K ids
      (GeneralFractionalBroadcast.program ids A L Δ r k t Q T s 7 q M hQ)).maxBits ≤
      max c (messageConstant a K A L Δ r k Q T s q M c) * Nat.clog 2 (n + 2) := by
  exact KT0Compiler.logarithmic_bits ids _ n c _ hids
    (logarithmic_bits ids a K A L Δ r k t Q T s q M hQ n c hids)

def roundConstant (a K A r k T M : ℕ) : ℕ :=
  (2 * A) * (4 + 2 * GeneralInitBroadcast.rank A) +
    (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M) +
    11 + SmallComponentProgram.roundBound a K

theorem port_uniform_rounds {b : ℕ} (ids : BitCode V b)
    (a K A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (portProgram 6 (PartialFractionalProgram.denominator Δ k Q T s q) a K ids
      (GeneralFractionalBroadcast.program ids A L Δ r k t Q T s 7 q M hQ)).rounds =
      roundConstant a K A r k T M := by
  rw [port_rounds, GeneralFractionalBroadcast.rounds]
  rfl

end Paper.SurfaceFinalProgram


