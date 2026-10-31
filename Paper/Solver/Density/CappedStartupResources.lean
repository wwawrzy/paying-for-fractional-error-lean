import Paper.Solver.Density.CappedOutputRegister

/-! Resources of the actual startup with a private output register.
The degree broadcast is the only communication step. Initializing the
private register is local and contributes zero rounds and zero bits. -/

namespace Paper.Density.CappedStartupResources

variable {V : Type} [DecidableEq V]

/-- Startup contains exactly one broadcast, including on an empty graph. -/
theorem startup_rounds (cap : ℚ) :
    (CappedOutputRegister.startup (V := V) cap).rounds = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The local initialization of the private register adds no message bits. -/
theorem startup_bits_eq (cap : ℚ) :
    (CappedOutputRegister.startup cap).maxBits G (fun _ => PUnit.unit) =
      (CappedSchedules.startup cap).maxBits G (fun _ => PUnit.unit) := by
  change max ((CappedSchedules.startup cap).maxBits G (fun _ => PUnit.unit)) 0 = _
  exact Nat.max_zero _

/-- The startup bound needs neither a degree bound nor a sign condition on cap. -/
theorem startup_bits (cap : ℚ) (m : ℕ) :
    (CappedOutputRegister.startup cap).maxBits G (fun _ => PUnit.unit) ≤
      (2 * m + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  have hlog : 1 ≤ Nat.clog 2 (Fintype.card V + 2) :=
    Nat.clog_pos (by decide) (by omega)
  apply PrefixBroadcast.Program.seq_bits_le
  · change (PrefixBroadcast.Program.broadcast
      (PrefixBroadcast.round PrefixCode.nat (CappedStartup.degreeRound cap))).maxBits G
        (fun _ => PUnit.unit) ≤ _
    apply PrefixBroadcast.Program.broadcast_bits_le
    intro v
    have h := CappedExecution.startup_message_length G cap v
    nlinarith
  · exact Nat.zero_le _

end Paper.Density.CappedStartupResources

#print axioms Paper.Density.CappedStartupResources.startup_rounds
#print axioms Paper.Density.CappedStartupResources.startup_bits_eq
#print axioms Paper.Density.CappedStartupResources.startup_bits
