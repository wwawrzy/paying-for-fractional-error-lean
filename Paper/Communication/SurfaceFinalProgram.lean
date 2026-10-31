import Paper.Communication.SurfaceResidualRounding
import Paper.Endpoints.Components.SurfacePreparedCases
import Paper.Endpoints.Rounding.SurfaceTwoBudget
namespace Paper.SurfaceFinalProgram
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

def initial {N : ℕ} (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    Program V (GeneralCoveringFractional.Input V 1) Bool :=
  .seq (.local fun _ _ _ => ()) (SurfaceResidualRounding.withSolver d D P)

def residual {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) : Program V Unit Bool :=
  .seq (SurfaceResidual.unitPrepare d)
    (ComponentReplacementProgram.program (initial d D P)
      (SmallComponentProgram.program ids a 1 K (by omega)))

theorem rounds {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (residual d D a K ids P).rounds = P.rounds + 8 +
      (SmallComponentProgram.program ids a 1 K (by omega)).rounds := by
  simp only [residual, Program.rounds, SurfaceResidual.unitPrepare_rounds,
    ComponentReplacementProgram.rounds, initial, SurfaceResidualRounding.withSolver_rounds]
  omega

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_initial {N : ℕ} (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N))
    (s : V → GeneralCoveringFractional.Input V 1) :
    (initial d D P).runEncoded G s =
      (SurfaceResidualRounding.withSolver d D P).runEncoded G (fun _ => ()) := by
  simp only [Program.runEncoded_eq_run, initial, Program.run]

theorem run_residual {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (residual d D a K ids P).runEncoded G (fun _ => ()) =
      (ComponentReplacementProgram.program (initial d D P)
        (SmallComponentProgram.program ids a 1 K (by omega))).runEncoded G (SurfaceResidual.unitInput G d) := by
  simp only [Program.runEncoded_eq_run, residual, Program.run]
  rw [SurfaceResidual.unitPrepare_correct]

def program {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) : Program V Unit Bool :=
  .seq (CurrentZoneProgram.program d)
    (.seq (.local fun _ _ e => ((), e.selected))
      (.seq (ProgramMemory.carry (residual d D a K ids P))
        (.local fun _ _ s => s.1 || s.2)))

theorem run_program {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program d D a K ids P).runEncoded G (fun _ => ()) = fun v =>
      (residual d D a K ids P).runEncoded G (fun _ => ()) v ||
        decide (v ∈ CurrentBudget.selected G d) := by
  simp only [Program.runEncoded_eq_run, program, Program.run]
  rw [CurrentZoneProgram.correct]
  simp only [ProgramMemory.run, CurrentZoneProgram.expected]

theorem output_union {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    Finset.univ.filter (fun v => (program d D a K ids P).runEncoded G (fun _ => ()) v = true) =
      CurrentBudget.selected G d ∪
        Finset.univ.filter (fun v => (residual d D a K ids P).runEncoded G (fun _ => ()) v = true) := by
  rw [run_program]
  ext v
  simp [or_comm]

theorem dominates {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (SurfaceResidual.cover G d) (CurrentBudget.demands G d)) (a : ℝ))
    (hc : GeneralCoveringIntegral.Covers (SurfaceResidual.cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun v => (SurfaceResidualRounding.withSolver d D P).runEncoded G (fun _ => ()) v = true))) :
    SevenFoundation.dominates G
      (Finset.univ.filter (fun v => (program d D a K ids P).runEncoded G (fun _ => ()) v = true)) := by
  rw [output_union, run_residual]
  apply SurfaceResidual.prepared_dominates G d a K ha hK hden ids (initial d D P)
  rwa [run_initial]

theorem total_rounds {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program d D a K ids P).rounds = P.rounds + 10 +
      (SmallComponentProgram.program ids a 1 K (by omega)).rounds := by
  simp only [program, Program.rounds, ProgramMemory.rounds, CurrentZoneProgram.rounds, rounds]
  omega

theorem card_bound {N bits : ℕ} (D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin 8) (Fin N)) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (e : ℝ) (hbudget : 1176 * e ≤ (K : ℝ))
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (SurfaceResidual.cover G 6) (CurrentBudget.demands G 6)) (a : ℝ))
    (hc : GeneralCoveringIntegral.Covers (SurfaceResidual.cover G 6) (CurrentBudget.demands G 6)
      (Finset.univ.filter (fun v => (SurfaceResidualRounding.withSolver 6 D P).runEncoded G (fun _ => ()) v = true)))
    (hr : (1 + 1/294 : ℝ) * (Finset.univ.filter (fun v =>
      (SurfaceResidualRounding.withSolver 6 D P).runEncoded G (fun _ => ()) v = true)).card ≤
      (1 + 1/588 : ℝ) * CurrentBudget.auxiliaryNumber G 6 + 2 * e)
    (Y : Finset V) (hY : SevenFoundation.dominates G Y) :
    (Finset.univ.filter (fun v => (program 6 D a K ids P).runEncoded G (fun _ => ()) v = true)).card ≤
      7 * Y.card := by
  have hc0 : GeneralCoveringIntegral.Covers (SurfaceResidual.cover G 6) (CurrentBudget.demands G 6)
      (Finset.univ.filter (fun v => (initial 6 D P).runEncoded G (SurfaceResidual.unitInput G 6) v = true)) := by
    rwa [run_initial]
  have hcases := SurfaceResidual.prepared_cases G 6 a K ha hK hden ids (initial 6 D P) hc0
  have hle := SurfaceResidual.prepared_card_le G 6 a K ha hK hden ids (initial 6 D P) hc0
  rw [run_initial, ← run_residual] at hcases hle
  have hi := SurfaceResidual.surface_unit_budget G Y hY
  have hf := CurrentBudget.fractional_budget G 6
  have hsum : ((CurrentBudget.selected G 6).card : ℝ) +
      (Finset.univ.filter (fun v => (residual 6 D a K ids P).runEncoded G (fun _ => ()) v = true)).card ≤
      7 * (Y.card : ℝ) := by
    apply SurfaceTwoBudget.two_budgets _ _ _
      (IntegralCoverOptimum.optimum (SurfaceResidual.cover G 6) (CurrentBudget.demands G 6) (fun _ => 1) : ℝ)
      _ _ (SevenFoundation.fractionalNumber G) e (by exact_mod_cast hle)
      (by exact_mod_cast hi) (by simpa using hf) (SevenFoundation.fractionalNumber_le_integral G Y hY) hr
    rcases hcases with hs | hl
    · left; exact_mod_cast hs
    · right
      exact lt_of_le_of_lt hbudget (by exact_mod_cast hl)
  rw [output_union]
  have hu := Finset.card_union_le (CurrentBudget.selected G 6)
    (Finset.univ.filter (fun v => (residual 6 D a K ids P).runEncoded G (fun _ => ()) v = true))
  have hn : (CurrentBudget.selected G 6).card +
      (Finset.univ.filter (fun v => (residual 6 D a K ids P).runEncoded G (fun _ => ()) v = true)).card ≤ 7 * Y.card := by
    exact_mod_cast hsum
  exact hu.trans hn

theorem total_maxBits {N bits : ℕ} (d D a K : ℕ) (ids : BitCode V bits)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program d D a K ids P).maxBits = max 1 (max P.maxBits
      (SmallComponentProgram.program ids a 1 K (by omega)).maxBits) := by
  simp [program, residual, initial, SurfaceResidualRounding.withSolver,
    Program.maxBits, ProgramMemory.maxBits, CurrentZoneProgram.maxBits,
    SurfaceResidual.unitPrepare_bits, ComponentReplacementProgram.maxBits,
    CurrentCriticalProgram.auxiliary_maxBits, SurfaceResidualRounding.maxBits,
    max_assoc, max_comm, max_left_comm]

end Paper.SurfaceFinalProgram


