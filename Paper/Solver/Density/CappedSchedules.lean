import Paper.Communication.PrefixProgram
import Paper.Solver.Density.CappedExecution

/-! Structural round counts and reachable-message bounds for finite prefixes
of the unknown-degree execution. A prefix length is used only in the proof;
the repeated update program itself receives no stopping horizon. -/
namespace Paper.Density.CappedSchedules
open CappedCounterState (State)
variable {V : Type} [DecidableEq V]

def startup (cap : ℚ) : PrefixBroadcast.Program V PUnit State :=
  .broadcast (PrefixBroadcast.round PrefixCode.nat (CappedStartup.degreeRound cap))

def update (cap : ℚ) (m : ℕ) (rho : ℚ) : PrefixBroadcast.Program V State State :=
  .seq (.broadcast (CappedEncodedRounds.tightRound cap m rho))
    (.broadcast (CappedEncodedRounds.freezeRound cap m))

def schedule (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) : PrefixBroadcast.Program V PUnit State :=
  .seq (startup cap) ((update cap m rho).iterate n)

theorem update_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) :
    (update (V := V) cap m rho).rounds = 2 := rfl

theorem schedule_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule (V := V) cap m rho n).rounds = 1+2*n := by
  change 1+((update (V := V) cap m rho).iterate n).rounds = _
  rw [PrefixBroadcast.Program.iterate_rounds, update_rounds, Nat.mul_comm]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem iterate_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    ((update cap m rho).iterate n).run G (CappedExecution.initial G cap) =
      CappedExecution.run G cap m rho n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PrefixBroadcast.Program.iterate_run_succ, ih]
    rfl

theorem schedule_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule cap m rho n).run G (fun _ => PUnit.unit) = CappedExecution.run G cap m rho n :=
  iterate_run G cap m rho n

theorem update_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta+extra) :
    (update cap m rho).maxBits G (CappedExecution.run G cap m rho n) ≤
      (2*m+2*extra+5)*Nat.clog 2 (Fintype.card V+2) := by
  have hH : 1 ≤ Nat.clog 2 (Fintype.card V+2) := Nat.clog_pos (by decide) (by omega)
  apply PrefixBroadcast.Program.seq_bits_le
  · apply PrefixBroadcast.Program.broadcast_bits_le
    exact CappedExecution.packet_length G cap m rho n Delta extra hdegree hD hn
  · apply PrefixBroadcast.Program.broadcast_bits_le
    intro v
    rw [CappedEncodedRounds.freeze_message_length]
    nlinarith

theorem iterate_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (n : ℕ) (hn : n ≤ CappedGrowth.timeBound m Delta+extra) :
    ((update cap m rho).iterate n).maxBits G (CappedExecution.initial G cap) ≤
      (2*m+2*extra+5)*Nat.clog 2 (Fintype.card V+2) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    apply PrefixBroadcast.Program.seq_bits_le
    · exact ih (by omega)
    · rw [iterate_run]
      exact update_bits G cap m rho n Delta extra hdegree hD (by omega)

theorem schedule_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta+extra) :
    (schedule cap m rho n).maxBits G (fun _ => PUnit.unit) ≤
      (2*m+2*extra+5)*Nat.clog 2 (Fintype.card V+2) := by
  have hH : 1 ≤ Nat.clog 2 (Fintype.card V+2) := Nat.clog_pos (by decide) (by omega)
  apply PrefixBroadcast.Program.seq_bits_le
  · apply PrefixBroadcast.Program.broadcast_bits_le
    intro v
    have h := CappedExecution.startup_message_length G cap v
    nlinarith
  · exact iterate_bits G cap m rho Delta extra hdegree hD n hn

end Paper.Density.CappedSchedules
#print axioms Paper.Density.CappedSchedules.schedule_run
#print axioms Paper.Density.CappedSchedules.schedule_rounds
#print axioms Paper.Density.CappedSchedules.schedule_bits
