import Paper.Communication.SurfaceGirthSolver
import Paper.Communication.OrdinaryAbsorptionPort
namespace Paper.SurfaceGirthResources
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
def roundConstant (a K A r k T M : ℕ) : ℕ :=
  1+((2*A)*(4+2*GeneralInitBroadcast.rank A)+
    (34+4*OwnerBoundaryMean.radius k T+4*r+RecursiveSearch.roundBound (4*k) A M)+1+
      SmallComponentProgram.roundBound a K)
def solverMessageConstant (A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max (max (1+GeneralInitBroadcast.rank A*(c+1))
    (PartialFractionalBudget.constant L Δ r k Q T s A 1 q M c)) 1
def messageConstant (a K A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max c (max (solverMessageConstant A L Δ r k Q T s q M c)
    (SmallComponentProgram.messageConstant a 1 K c))
theorem uniform_rounds {b : ℕ} (ids : BitCode V b)
    (a K g A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (OrdinaryAbsorption.portProgram ids a K
      (SurfaceGirthSolver.program (CappedWholeProgram.program ids A L Δ r k t Q T s q M hQ)
        (PartialFractionalProgram.denominator Δ k Q T s q) g)).rounds =
      roundConstant a K A r k T M := by
  rw [OrdinaryAbsorption.port_rounds,SurfaceGirthSolver.rounds,CappedWholeProgram.rounds]
  rfl
theorem logarithmic_bits {b : ℕ} (ids : BitCode V b)
    (a K g A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (n c : ℕ)
    (hids : b ≤ c*Nat.clog 2 (n+2)) :
    (OrdinaryAbsorption.portProgram ids a K
      (SurfaceGirthSolver.program (CappedWholeProgram.program ids A L Δ r k t Q T s q M hQ)
        (PartialFractionalProgram.denominator Δ k Q T s q) g)).maxBits ≤
      messageConstant a K A L Δ r k Q T s q M c * Nat.clog 2 (n+2) := by
  apply OrdinaryAbsorption.port_bits ids a K _ n c
    (solverMessageConstant A L Δ r k Q T s q M c) hids
  rw [SurfaceGirthSolver.maxBits,CappedWholeProgram.maxBits]
  have hp := GeneralFractionalBroadcast.logarithmic_bits ids A L Δ r k t Q T s 1 q M hQ n c hids
  have hl : 1 ≤ Nat.clog 2 (n+2) := Nat.clog_pos (by omega) (by omega)
  have h1 : 1 ≤ solverMessageConstant A L Δ r k Q T s q M c := le_max_right _ _
  have hc : max (1+GeneralInitBroadcast.rank A*(c+1))
      (PartialFractionalBudget.constant L Δ r k Q T s A 1 q M c) ≤
      solverMessageConstant A L Δ r k Q T s q M c := le_max_left _ _
  exact max_le (hp.trans (Nat.mul_le_mul_right _ hc)) (by nlinarith)
end Paper.SurfaceGirthResources
#print axioms Paper.SurfaceGirthResources.uniform_rounds
#print axioms Paper.SurfaceGirthResources.logarithmic_bits
