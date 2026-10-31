import Paper.Solver.Density.CappedSchedules
import Paper.Solver.Density.CappedHaltRounds

/-! Uniform repeated phases with an observable halt probe at every update
index. Probes preserve the compact state. A phase performs four certificate
broadcasts followed by two update broadcasts. Prefix indices and degree
bounds occur only in execution and resource analysis, not in instructions.
Completion and irrevocable output are separate theorems. -/

namespace Paper.Density.CappedProtocolSchedules

open CappedCounterState (State)

variable {V : Type} [DecidableEq V]

def phase (cap : ℚ) (m : ℕ) (rho : ℚ) : PrefixBroadcast.Program V State State :=
  .seq (CappedHaltRounds.program cap m rho)
    (.seq (.local (fun _ _ r => r.state)) (CappedSchedules.update cap m rho))

def statePrefix (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) : PrefixBroadcast.Program V PUnit State :=
  .seq (CappedSchedules.startup cap) ((phase cap m rho).iterate n)

def schedule (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    PrefixBroadcast.Program V PUnit CappedHaltRounds.Result :=
  .seq (statePrefix cap m rho n) (CappedHaltRounds.program cap m rho)

theorem phase_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) :
    (phase (V := V) cap m rho).rounds = 6 := by
  change (CappedHaltRounds.program (V := V) cap m rho).rounds +
    (0 + (CappedSchedules.update (V := V) cap m rho).rounds) = 6
  rw [CappedHaltRounds.program_rounds, CappedSchedules.update_rounds]

theorem prefix_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (statePrefix (V := V) cap m rho n).rounds = 1 + 6 * n := by
  change 1 + ((phase (V := V) cap m rho).iterate n).rounds = _
  rw [PrefixBroadcast.Program.iterate_rounds, phase_rounds, Nat.mul_comm]

theorem schedule_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule (V := V) cap m rho n).rounds = 1 + 6 * n + 4 := by
  change (statePrefix (V := V) cap m rho n).rounds +
    (CappedHaltRounds.program (V := V) cap m rho).rounds = _
  rw [prefix_rounds, CappedHaltRounds.program_rounds]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem probe_preserves (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) :
    (fun v => ((CappedHaltRounds.program cap m rho).run G s v).state) = s := by
  funext v
  rw [CappedHaltRounds.program_run_eq]
  exact CappedHaltRounds.probe_state G cap m rho s v

theorem phase_run (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) :
    (phase cap m rho).run G s = CappedEncodedRounds.transition G cap m rho s := by
  change (CappedSchedules.update cap m rho).run G
    (fun v => ((CappedHaltRounds.program cap m rho).run G s v).state) = _
  rw [probe_preserves]
  rfl

theorem iterate_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    ((phase cap m rho).iterate n).run G (CappedExecution.initial G cap) =
      CappedExecution.run G cap m rho n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PrefixBroadcast.Program.iterate_run_succ, ih, phase_run]
    rfl

theorem prefix_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (statePrefix cap m rho n).run G (fun _ => PUnit.unit) = CappedExecution.run G cap m rho n :=
  iterate_run G cap m rho n

/-- The nth observable probe examines exactly the nth actual update state. -/
theorem schedule_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule cap m rho n).run G (fun _ => PUnit.unit) =
      CappedHaltRounds.probe G cap m rho (CappedExecution.run G cap m rho n) := by
  change (CappedHaltRounds.program cap m rho).run G
    ((statePrefix cap m rho n).run G (fun _ => PUnit.unit)) = _
  rw [prefix_run, CappedHaltRounds.program_run_eq]

theorem probe_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    (CappedHaltRounds.program cap m rho).maxBits G (CappedExecution.run G cap m rho n) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  have hH : 1 ≤ Nat.clog 2 (Fintype.card V + 2) := Nat.clog_pos (by decide) (by omega)
  apply CappedHaltRounds.program_bits_le
  · nlinarith
  · exact CappedExecution.packet_length G cap m rho n Delta extra hdegree hD hn

theorem phase_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    (phase cap m rho).maxBits G (CappedExecution.run G cap m rho n) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  unfold phase
  apply PrefixBroadcast.Program.seq_bits_le
  · exact probe_bits G cap m rho n Delta extra hdegree hD hn
  · apply PrefixBroadcast.Program.seq_bits_le
    · exact Nat.zero_le _
    · change (CappedSchedules.update cap m rho).maxBits G
        (fun v => ((CappedHaltRounds.program cap m rho).run G
          (CappedExecution.run G cap m rho n) v).state) ≤ _
      rw [probe_preserves]
      exact CappedSchedules.update_bits G cap m rho n Delta extra hdegree hD hn

theorem iterate_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (n : ℕ) (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    ((phase cap m rho).iterate n).maxBits G (CappedExecution.initial G cap) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    apply PrefixBroadcast.Program.seq_bits_le
    · exact ih (by omega)
    · rw [iterate_run]
      exact phase_bits G cap m rho n Delta extra hdegree hD (by omega)

theorem prefix_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    (statePrefix cap m rho n).maxBits G (fun _ => PUnit.unit) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  apply PrefixBroadcast.Program.seq_bits_le
  · have h := CappedSchedules.schedule_bits G cap m rho 0 Delta extra hdegree hD (by omega)
    simpa only [CappedSchedules.schedule, PrefixBroadcast.Program.maxBits,
      PrefixBroadcast.Program.iterate, Nat.max_zero] using h
  · exact iterate_bits G cap m rho Delta extra hdegree hD n hn

theorem schedule_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    (schedule cap m rho n).maxBits G (fun _ => PUnit.unit) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  apply PrefixBroadcast.Program.seq_bits_le
  · exact prefix_bits G cap m rho n Delta extra hdegree hD hn
  · rw [prefix_run]
    exact probe_bits G cap m rho n Delta extra hdegree hD hn

end Paper.Density.CappedProtocolSchedules

#print axioms Paper.Density.CappedProtocolSchedules.phase_run
#print axioms Paper.Density.CappedProtocolSchedules.schedule_run
#print axioms Paper.Density.CappedProtocolSchedules.schedule_rounds
#print axioms Paper.Density.CappedProtocolSchedules.schedule_bits
