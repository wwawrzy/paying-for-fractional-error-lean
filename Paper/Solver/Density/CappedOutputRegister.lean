import Paper.Solver.Density.CappedProtocolSchedules
import Paper.Communication.PrefixCarry

/-! An actual private output register for the uniform capped protocol.
The first successful probe records its output bit; later phases retain it.
The register is carried privately and does not alter broadcast messages.
Correctness of completed output bits is a separate completion theorem. -/

namespace Paper.Density.CappedOutputRegister

open CappedCounterState (State)

def latch (old : Option Bool) (r : CappedHaltRounds.Result) : Option Bool :=
  match old with
  | some b => some b
  | none => if r.done then some r.output else none

variable {V : Type} [DecidableEq V]

def inspect (cap : ℚ) (m : ℕ) (rho : ℚ) :
    PrefixBroadcast.Program V (State × Option Bool) (State × Option Bool) :=
  .seq ((CappedHaltRounds.program cap m rho).carry (Option Bool))
    (.local (fun _ _ s => (s.1.state, latch s.2 s.1)))

def phase (cap : ℚ) (m : ℕ) (rho : ℚ) :
    PrefixBroadcast.Program V (State × Option Bool) (State × Option Bool) :=
  .seq (inspect cap m rho) ((CappedSchedules.update cap m rho).carry (Option Bool))

def startup (cap : ℚ) : PrefixBroadcast.Program V PUnit (State × Option Bool) :=
  .seq (CappedSchedules.startup cap) (.local (fun _ _ s => (s, none)))

def statePrefix (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    PrefixBroadcast.Program V PUnit (State × Option Bool) :=
  .seq (startup cap) ((phase cap m rho).iterate n)

def schedule (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    PrefixBroadcast.Program V PUnit (State × Option Bool) :=
  .seq (statePrefix cap m rho n) (inspect cap m rho)

theorem inspect_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) :
    (inspect (V := V) cap m rho).rounds = 4 := by
  change ((CappedHaltRounds.program (V := V) cap m rho).carry (Option Bool)).rounds + 0 = 4
  rw [PrefixBroadcast.Program.carry_rounds, CappedHaltRounds.program_rounds]

theorem phase_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) :
    (phase (V := V) cap m rho).rounds = 6 := by
  change (inspect (V := V) cap m rho).rounds +
    ((CappedSchedules.update (V := V) cap m rho).carry (Option Bool)).rounds = 6
  rw [inspect_rounds, PrefixBroadcast.Program.carry_rounds, CappedSchedules.update_rounds]

theorem schedule_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule (V := V) cap m rho n).rounds = 1 + 6 * n + 4 := by
  change (1 + ((phase (V := V) cap m rho).iterate n).rounds) +
    (inspect (V := V) cap m rho).rounds = _
  rw [PrefixBroadcast.Program.iterate_rounds, phase_rounds, inspect_rounds, Nat.mul_comm]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def before (cap : ℚ) (m : ℕ) (rho : ℚ) : ℕ → V → Option Bool
  | 0 => fun _ => none
  | n + 1 => fun v => latch (before cap m rho n v)
      (CappedHaltRounds.probe G cap m rho (CappedExecution.run G cap m rho n) v)

def reported (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) (v : V) : Option Bool :=
  latch (before G cap m rho n v)
    (CappedHaltRounds.probe G cap m rho (CappedExecution.run G cap m rho n) v)

theorem inspect_run (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State × Option Bool) :
    (inspect cap m rho).run G s = fun v =>
      ((s v).1, latch (s v).2 (CappedHaltRounds.probe G cap m rho (fun u => (s u).1) v)) := by
  change (fun v =>
    ((((CappedHaltRounds.program cap m rho).carry (Option Bool)).run G s v).1.state,
      latch (((CappedHaltRounds.program cap m rho).carry (Option Bool)).run G s v).2
        (((CappedHaltRounds.program cap m rho).carry (Option Bool)).run G s v).1)) = _
  rw [PrefixBroadcast.Program.carry_run, CappedHaltRounds.program_run_eq]
  funext v
  rw [CappedHaltRounds.probe_state]

theorem phase_run (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State × Option Bool) :
    (phase cap m rho).run G s = fun v =>
      (CappedEncodedRounds.transition G cap m rho (fun u => (s u).1) v,
        latch (s v).2 (CappedHaltRounds.probe G cap m rho (fun u => (s u).1) v)) := by
  change ((CappedSchedules.update cap m rho).carry (Option Bool)).run G
    ((inspect cap m rho).run G s) = _
  rw [PrefixBroadcast.Program.carry_run, inspect_run]
  rfl

theorem iterate_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    ((phase cap m rho).iterate n).run G (fun v => (CappedExecution.initial G cap v, none)) =
      fun v => (CappedExecution.run G cap m rho n v, before G cap m rho n v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PrefixBroadcast.Program.iterate_run_succ, ih, phase_run]
    rfl

theorem prefix_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (statePrefix cap m rho n).run G (fun _ => PUnit.unit) =
      fun v => (CappedExecution.run G cap m rho n v, before G cap m rho n v) :=
  iterate_run G cap m rho n

/-- The transmitted computation and private register agree with the exact
recursive first-success latch on every observed probe. -/
theorem schedule_run (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule cap m rho n).run G (fun _ => PUnit.unit) =
      fun v => (CappedExecution.run G cap m rho n v, reported G cap m rho n v) := by
  change (inspect cap m rho).run G ((statePrefix cap m rho n).run G (fun _ => PUnit.unit)) = _
  rw [prefix_run, inspect_run]
  rfl

theorem inspect_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State × Option Bool) :
    (inspect cap m rho).maxBits G s =
      (CappedHaltRounds.program cap m rho).maxBits G (fun v => (s v).1) := by
  change max (((CappedHaltRounds.program cap m rho).carry (Option Bool)).maxBits G s) 0 = _
  rw [PrefixBroadcast.Program.carry_bits, Nat.max_zero]

theorem phase_bits_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State × Option Bool) :
    (phase cap m rho).maxBits G s =
      (CappedProtocolSchedules.phase cap m rho).maxBits G (fun v => (s v).1) := by
  change max ((inspect cap m rho).maxBits G s)
    (((CappedSchedules.update cap m rho).carry (Option Bool)).maxBits G
      ((inspect cap m rho).run G s)) =
    max ((CappedHaltRounds.program cap m rho).maxBits G (fun v => (s v).1))
      (max 0 ((CappedSchedules.update cap m rho).maxBits G
        (fun v => ((CappedHaltRounds.program cap m rho).run G (fun u => (s u).1) v).state)))
  rw [inspect_bits, PrefixBroadcast.Program.carry_bits, inspect_run,
    CappedProtocolSchedules.probe_preserves, Nat.zero_max]

theorem iterate_bits_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    ((phase cap m rho).iterate n).maxBits G (fun v => (CappedExecution.initial G cap v, none)) =
      ((CappedProtocolSchedules.phase cap m rho).iterate n).maxBits G
        (CappedExecution.initial G cap) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change max (((phase cap m rho).iterate n).maxBits G
      (fun v => (CappedExecution.initial G cap v, none)))
      ((phase cap m rho).maxBits G (((phase cap m rho).iterate n).run G
        (fun v => (CappedExecution.initial G cap v, none)))) =
      max (((CappedProtocolSchedules.phase cap m rho).iterate n).maxBits G
        (CappedExecution.initial G cap))
        ((CappedProtocolSchedules.phase cap m rho).maxBits G
          (((CappedProtocolSchedules.phase cap m rho).iterate n).run G
            (CappedExecution.initial G cap)))
    rw [ih, iterate_run, CappedProtocolSchedules.iterate_run, phase_bits_eq]

theorem prefix_bits_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (statePrefix cap m rho n).maxBits G (fun _ => PUnit.unit) =
      (CappedProtocolSchedules.statePrefix cap m rho n).maxBits G (fun _ => PUnit.unit) := by
  change max (max ((CappedSchedules.startup cap).maxBits G (fun _ => PUnit.unit)) 0)
    (((phase cap m rho).iterate n).maxBits G (fun v => (CappedExecution.initial G cap v, none))) =
    max ((CappedSchedules.startup cap).maxBits G (fun _ => PUnit.unit))
      (((CappedProtocolSchedules.phase cap m rho).iterate n).maxBits G (CappedExecution.initial G cap))
  rw [Nat.max_zero, iterate_bits_eq]

/-- The private output register changes neither packet nor control width. -/
theorem schedule_bits_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) :
    (schedule cap m rho n).maxBits G (fun _ => PUnit.unit) =
      (CappedProtocolSchedules.schedule cap m rho n).maxBits G (fun _ => PUnit.unit) := by
  change max ((statePrefix cap m rho n).maxBits G (fun _ => PUnit.unit))
    ((inspect cap m rho).maxBits G ((statePrefix cap m rho n).run G (fun _ => PUnit.unit))) =
    max ((CappedProtocolSchedules.statePrefix cap m rho n).maxBits G (fun _ => PUnit.unit))
      ((CappedHaltRounds.program cap m rho).maxBits G
        ((CappedProtocolSchedules.statePrefix cap m rho n).run G (fun _ => PUnit.unit)))
  rw [prefix_bits_eq, inspect_bits, prefix_run, CappedProtocolSchedules.prefix_run]

theorem schedule_bits (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    (schedule cap m rho n).maxBits G (fun _ => PUnit.unit) ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  rw [schedule_bits_eq]
  exact CappedProtocolSchedules.schedule_bits G cap m rho n Delta extra hdegree hD hn

end Paper.Density.CappedOutputRegister

#print axioms Paper.Density.CappedOutputRegister.schedule_run
#print axioms Paper.Density.CappedOutputRegister.schedule_rounds
#print axioms Paper.Density.CappedOutputRegister.schedule_bits_eq
#print axioms Paper.Density.CappedOutputRegister.schedule_bits
