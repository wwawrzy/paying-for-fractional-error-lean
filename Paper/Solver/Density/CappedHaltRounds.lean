import Paper.Solver.Density.CappedStateCode
import Paper.Solver.Density.CappedPacketRounds
import Paper.Solver.Density.CappedLocalHalt
import Paper.Communication.PrefixProgram

/-! A four-broadcast local halt probe on a fixed compact-state vector.
The first broadcast is an encoded state packet; the remaining broadcasts
each send one Boolean. The probe computes output and the two-hop finished
certificate from actual decoded values, with no terminal-state premise. -/

namespace Paper.Density.CappedHaltRounds

open BroadcastModel SevenFoundation
open CappedCounterState (State decode)

structure Status where
  state : State
  output : Bool
  finished : Bool

structure NearStatus where
  status : Status
  near : Bool

structure Result where
  state : State
  output : Bool
  done : Bool

variable {V : Type} [DecidableEq V]

def rawStatusRound (cap : ℚ) (m : ℕ) : Round V (State × Bool) Status Bool where
  send _ _ s := s.2
  update _ N s msg :=
    let blocked := s.2 = true ∨ ∃ u : N, msg u = true
    ⟨s.1, decide (s.2 = true ∨ ¬ blocked), decide (blocked ∨ decode cap m s.1 = cap)⟩

def rawNearRound : Round V Status NearStatus Bool where
  send _ _ s := s.finished
  update _ N s msg := ⟨s, decide (s.finished = true ∧ ∀ u : N, msg u = true)⟩

def rawDoneRound : Round V NearStatus Result Bool where
  send _ _ s := s.near
  update _ N s msg :=
    ⟨s.status.state, s.status.output, decide (s.near = true ∧ ∀ u : N, msg u = true)⟩

def tightRound (cap : ℚ) (m : ℕ) (rho : ℚ) : Round V State (State × Bool) (List Bool) :=
  PrefixBroadcast.round CappedStateCode.code (CappedPacketRounds.tightRound cap m rho)

def statusRound (cap : ℚ) (m : ℕ) : Round V (State × Bool) Status (List Bool) :=
  PrefixBroadcast.round PrefixCode.bool (rawStatusRound cap m)

def nearRound : Round V Status NearStatus (List Bool) :=
  PrefixBroadcast.round PrefixCode.bool rawNearRound

def doneRound : Round V NearStatus Result (List Bool) :=
  PrefixBroadcast.round PrefixCode.bool rawDoneRound

def program (cap : ℚ) (m : ℕ) (rho : ℚ) : PrefixBroadcast.Program V State Result :=
  .seq (.broadcast (tightRound cap m rho))
    (.seq (.broadcast (statusRound cap m))
      (.seq (.broadcast nearRound) (.broadcast doneRound)))

omit [DecidableEq V] in
theorem program_rounds (cap : ℚ) (m : ℕ) (rho : ℚ) :
    (program (V := V) cap m rho).rounds = 4 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def statuses (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → Status :=
  eval G (rawStatusRound cap m) (eval G (CappedPacketRounds.tightRound cap m rho) s)

def nearStatuses (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → NearStatus :=
  eval G rawNearRound (statuses G cap m rho s)

def rawProbe (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → Result :=
  eval G rawDoneRound (nearStatuses G cap m rho s)

/-- Four explicit sequential encoded broadcasts; the values remain fixed. -/
def probe (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → Result :=
  eval G doneRound (eval G nearRound
    (eval G (statusRound cap m) (eval G (tightRound cap m rho) s)))

theorem program_run_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) :
    (program cap m rho).run G s = probe G cap m rho s := rfl

theorem probe_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) :
    probe G cap m rho s = rawProbe G cap m rho s := by
  unfold probe doneRound nearRound statusRound tightRound
  rw [PrefixBroadcast.eval_eq, PrefixBroadcast.eval_eq,
    PrefixBroadcast.eval_eq, PrefixBroadcast.eval_eq]
  rfl

theorem all_closed_iff (f : V → Bool) (v : V) :
    (f v = true ∧ ∀ u : G.neighborFinset v, f u = true) ↔
      ∀ u ∈ closed G v, f u = true := by
  constructor
  · rintro ⟨hv, hn⟩ u hu
    rcases (mem_closed G u v).mp hu with he | ha
    · simpa only [he] using hv
    · exact hn ⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr ha⟩
  · intro h
    exact ⟨h v (self_mem_closed G v), fun u =>
      h u ((mem_closed G u v).mpr
        (Or.inr ((SimpleGraph.mem_neighborFinset G v u).mp u.property)))⟩

theorem statuses_state (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (statuses G cap m rho s v).state = s v := rfl

theorem statuses_finished (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (statuses G cap m rho s v).finished = true ↔
      CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
        (fun u => (decode cap m (s u) : ℝ)) v := by
  let y := fun u => decode cap m (s u)
  let tight := eval G (CappedRationalRounds.tightRound rho) y
  change decide (((tight v).2 = true ∨
      ∃ u : G.neighborFinset v, (tight u).2 = true) ∨ y v = cap) = true ↔
    CappedDynamics.blocked G (rho : ℝ) (fun u => (y u : ℝ)) v ∨ (y v : ℝ) = (cap : ℝ)
  rw [decide_eq_true_eq, CappedRationalRounds.freeze_test]
  simp only [Rat.cast_inj]

theorem statuses_output (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (statuses G cap m rho s v).output = CappedLocalHalt.outputBit G (rho : ℝ)
      (fun u => (decode cap m (s u) : ℝ)) v := by
  classical
  let y := fun u => decode cap m (s u)
  let tight := eval G (CappedRationalRounds.tightRound rho) y
  have ht : (tight v).2 = true ↔
      (rho : ℝ) ≤ UnitDomination.mass G (fun u => (y u : ℝ)) v := by
    rw [← CappedRationalRounds.mass_cast]
    exact (CappedRationalRounds.tightRound_flag G rho y v).trans Rat.cast_le.symm
  change decide ((tight v).2 = true ∨ ¬ ((tight v).2 = true ∨
      ∃ u : G.neighborFinset v, (tight u).2 = true)) =
    decide ((rho : ℝ) ≤ UnitDomination.mass G (fun u => (y u : ℝ)) v ∨
      ¬ CappedDynamics.blocked G (rho : ℝ) (fun u => (y u : ℝ)) v)
  apply Bool.decide_congr
  exact or_congr ht (not_congr (CappedRationalRounds.freeze_test G rho y v))

theorem near_iff (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (nearStatuses G cap m rho s v).near = true ↔
      ∀ u ∈ closed G v, CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
        (fun w => (decode cap m (s w) : ℝ)) u := by
  change decide ((statuses G cap m rho s v).finished = true ∧
    ∀ u : G.neighborFinset v, (statuses G cap m rho s u).finished = true) = true ↔ _
  rw [decide_eq_true_eq, all_closed_iff G (fun u => (statuses G cap m rho s u).finished) v]
  simp only [statuses_finished]

theorem probe_state (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (probe G cap m rho s v).state = s v := by
  rw [probe_eq]
  rfl

theorem probe_output (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (probe G cap m rho s v).output = CappedLocalHalt.outputBit G (rho : ℝ)
      (fun u => (decode cap m (s u) : ℝ)) v := by
  rw [probe_eq]
  exact statuses_output G cap m rho s v

theorem probe_done_iff (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (probe G cap m rho s v).done = true ↔
      CappedLocalHalt.certificate G (cap : ℝ) (rho : ℝ)
        (fun u => (decode cap m (s u) : ℝ)) v := by
  rw [probe_eq]
  change decide ((nearStatuses G cap m rho s v).near = true ∧
    ∀ u : G.neighborFinset v, (nearStatuses G cap m rho s u).near = true) = true ↔ _
  rw [decide_eq_true_eq, all_closed_iff G (fun u => (nearStatuses G cap m rho s u).near) v]
  simp only [near_iff, CappedLocalHalt.certificate]

omit [DecidableEq V] in
theorem tight_message_bound (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State)
    (Delta extra : ℕ) (hdegree : Delta ≤ Fintype.card V)
    (hden : ∀ v, (s v).denominator ≤ Delta + 1)
    (hexp : ∀ v, (s v).exponent ≤ CappedGrowth.timeBound m Delta + extra) (v : V) :
    ((tightRound cap m rho).send v (G.neighborFinset v) (s v)).length ≤
      (2 * m + 2 * extra + 5) * Nat.clog 2 (Fintype.card V + 2) :=
  CappedStateCode.logarithmic_length m Delta (Fintype.card V) extra (s v)
    hdegree (hden v) (hexp v)

omit [DecidableEq V] [Fintype V] in
theorem status_message_length (cap : ℚ) (m : ℕ) (v : V) (N : Finset V) (s : State × Bool) :
    ((statusRound cap m).send v N s).length = 1 := rfl

omit [DecidableEq V] [Fintype V] in
theorem near_message_length (v : V) (N : Finset V) (s : Status) :
    (nearRound.send v N s).length = 1 := rfl

omit [DecidableEq V] [Fintype V] in
theorem done_message_length (v : V) (N : Finset V) (s : NearStatus) :
    (doneRound.send v N s).length = 1 := rfl

/-- The measured execution width is bounded by the packet budget whenever
that budget also allows the three one-bit control broadcasts. -/
theorem program_bits_le (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (b : ℕ)
    (hb : 1 ≤ b)
    (hpacket : ∀ v, ((tightRound cap m rho).send v (G.neighborFinset v) (s v)).length ≤ b) :
    (program cap m rho).maxBits G s ≤ b := by
  unfold program
  apply PrefixBroadcast.Program.seq_bits_le G
  · exact PrefixBroadcast.Program.broadcast_bits_le G _ s b hpacket
  · apply PrefixBroadcast.Program.seq_bits_le G
    · apply PrefixBroadcast.Program.broadcast_bits_le G
      intro v
      rw [status_message_length]
      exact hb
    · apply PrefixBroadcast.Program.seq_bits_le G
      · apply PrefixBroadcast.Program.broadcast_bits_le G
        intro v
        rw [near_message_length]
        exact hb
      · apply PrefixBroadcast.Program.broadcast_bits_le G
        intro v
        rw [done_message_length]
        exact hb

end Paper.Density.CappedHaltRounds

#print axioms Paper.Density.CappedHaltRounds.probe_state
#print axioms Paper.Density.CappedHaltRounds.probe_output
#print axioms Paper.Density.CappedHaltRounds.probe_done_iff
#print axioms Paper.Density.CappedHaltRounds.tight_message_bound
#print axioms Paper.Density.CappedHaltRounds.program_rounds
#print axioms Paper.Density.CappedHaltRounds.program_bits_le
