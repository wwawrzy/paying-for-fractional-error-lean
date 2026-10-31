import Paper.Communication.CurrentCriticalProgram
import Paper.Endpoints.Rounding.SurfaceResidualBudget
import Paper.Communication.CurrentThresholdProgram
namespace Paper.SurfaceResidualRounding
open Paper.BroadcastModel Paper.SevenFoundation
variable {V : Type} [DecidableEq V]

def program (d D N : ℕ) : Program V (Fin N × CurrentZoneProgram.Env d) Bool :=
  .seq (.local fun _ _ s => (s, s.2.candidate))
    (.seq (ProgramMemory.carry (CurrentThresholdProgram.program d D N))
      (.local fun _ _ s => s.1 && s.2))

theorem rounds (d D N : ℕ) : (program (V := V) d D N).rounds = 3 := by
  simp [program, Program.rounds, ProgramMemory.rounds, CurrentThresholdProgram.rounds]

theorem maxBits (d D N : ℕ) : (program (V := V) d D N).maxBits = 1 := by
  simp [program, Program.maxBits, ProgramMemory.maxBits, CurrentThresholdProgram.maxBits]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    (program d D N).run G (fun v => (p v, CurrentZoneProgram.expected G d v)) =
      fun v => decide (v ∈ CurrentRounding.output G a (CurrentCounting.input G a d hd
          (fun v => ((p v).val : ℝ) / D) hx hcap)) := by
  simp only [program, Program.run, ProgramMemory.run]
  rw [CurrentThresholdProgram.correct G d D N hD a hd p hx hcap]
  funext v
  apply Bool.eq_iff_iff.mpr
  have hs := CurrentRounding.output_subset G a (CurrentCounting.input G a d hd
    (fun v => ((p v).val : ℝ) / D) hx hcap)
  change _ ⊆ CurrentBudget.candidates G d at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, CurrentZoneProgram.expected,
    Finset.mem_union, CurrentBudget.selected, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact False.elim (h hc)
    · exact h
  · intro h
    exact ⟨Or.inr h, hs h⟩
theorem covers (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    GeneralCoveringIntegral.Covers (SurfaceResidual.cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun v => (program d D N).runEncoded G
        (fun u => (p u, CurrentZoneProgram.expected G d u)) v = true)) := by
  classical
  rw [Program.runEncoded_eq_run, correct G d D N hD a hd p hx hcap]
  let I := CurrentCounting.input G a d hd (fun v => ((p v).val : ℝ) / D) hx hcap
  intro r hr
  have hc := CurrentRounding.output_covers G a I hr
  obtain ⟨v, hv, hrv⟩ := Finset.mem_biUnion.mp hc
  refine ⟨v, ?_, ?_⟩
  · simpa using hv
  · exact Finset.mem_inter.mpr ⟨(closed_symm G r v).mp hrv,
      CurrentRounding.output_subset G a I hv⟩

def withSolver {N : ℕ} (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) : Program V Unit Bool :=
  .seq (CurrentCriticalProgram.auxiliaryProgram d D P) (program d D (D + 1))

theorem withSolver_rounds {N : ℕ} (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (withSolver d D P).rounds = P.rounds + 5 := by
  simp only [withSolver, Program.rounds, CurrentCriticalProgram.auxiliary_rounds, rounds]

theorem withSolver_covers {N : ℕ} (d D : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (P : Program V (Bool × Fin (d + 2)) (Fin N))
    (hx : feasible (CurrentBudget.auxiliary G d)
      (fun v => ((CurrentCriticalProgram.numerators G d D P v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d,
      ((CurrentCriticalProgram.numerators G d D P v).val : ℝ) / D ≤ 1) :
    GeneralCoveringIntegral.Covers (SurfaceResidual.cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun v => (withSolver d D P).runEncoded G (fun _ => ()) v = true)) := by
  have h := covers G d D (D + 1) hD a hd (CurrentCriticalProgram.numerators G d D P) hx hcap
  simp only [Program.runEncoded_eq_run] at h ⊢
  change GeneralCoveringIntegral.Covers _ _ (Finset.univ.filter (fun v =>
    (program d D (D + 1)).run G ((CurrentCriticalProgram.auxiliaryProgram d D P).run G (fun _ => ())) v = true))
  rw [CurrentCriticalProgram.auxiliary_run]
  exact h

theorem from_partial_spec {N : ℕ} (d D : ℕ) (hD : 0 < D) (a δ : ℝ)
    (hd : (d : ℝ) = 2 * a) (P : Program V (Bool × Fin (d + 2)) (Fin N))
    (hraw : PartialOptimum.Feasible G (CurrentBudget.demands G d)
        (fun v => ((CurrentCriticalProgram.raw G d P v).val : ℝ) / D))
    (hcost : PartialOptimum.objective (CurrentCriticalProgram.weights G d)
        (fun v => ((CurrentCriticalProgram.raw G d P v).val : ℝ) / D) ≤
      (1 + δ) * PartialOptimum.number G (CurrentBudget.demands G d)
        (CurrentCriticalProgram.weights G d)) :
    GeneralCoveringIntegral.Covers (SurfaceResidual.cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun v => (withSolver d D P).runEncoded G (fun _ => ()) v = true)) ∧
    cost (CurrentBudget.auxiliary G d)
      (fun v => ((CurrentCriticalProgram.numerators G d D P v).val : ℝ) / D) ≤
      (1 + δ) * CurrentBudget.auxiliaryNumber G d := by
  have hs := CurrentCriticalProgram.cap_restrict_spec G d _ hraw δ hcost
  have he := CurrentCriticalProgram.project_value G d D hD (CurrentCriticalProgram.raw G d P)
  change (fun v => ((CurrentCriticalProgram.numerators G d D P v).val : ℝ) / D) = _ at he
  rw [← he] at hs
  exact ⟨withSolver_covers G d D hD a hd P hs.1 (fun v _ => hs.2.1 v), hs.2.2⟩

end Paper.SurfaceResidualRounding
