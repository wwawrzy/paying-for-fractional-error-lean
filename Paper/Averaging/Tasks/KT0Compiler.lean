import Paper.Communication.PortDiscovery
import Paper.Communication.EncodedProgram

/-! Compile any KT1 broadcast program to KT0. First exchange own IDs,
then reconstruct each old local neighbor list and route each old incoming
message through the learned local port table. No graph is passed to code. -/
namespace Paper.KT0Compiler
variable {V : Type} [DecidableEq V]

def simulateRound {In Out Msg : Type} {b : ℕ} (C : BroadcastModel.BitCode Msg b)
    (R : BroadcastModel.Round V In Out Msg) :
    PortBroadcastModel.Program V (In × PortDiscovery.Env V) (Out × PortDiscovery.Env V) :=
  .broadcast b C {
    send := fun v _ st => R.send v (PortDiscovery.neighbors st.2) st.1
    update := fun v d st incoming =>
      (R.update v (PortDiscovery.neighbors st.2) st.1 (fun u =>
        PortDiscovery.read st.2 d incoming (R.send v (PortDiscovery.neighbors st.2) st.1) u.val), st.2) }

def translate {In Out : Type} : BroadcastModel.Program V In Out →
    PortBroadcastModel.Program V (In × PortDiscovery.Env V) (Out × PortDiscovery.Env V)
  | .local f => .local fun v _ st => (f v (PortDiscovery.neighbors st.2) st.1, st.2)
  | .broadcast _ C R => simulateRound C R
  | .seq P Q => .seq (translate P) (translate Q)

def execute {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) :
    PortBroadcastModel.Program V In (Out × PortDiscovery.Env V) :=
  .seq (PortDiscovery.prepare C) (translate P)

def program {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) : PortBroadcastModel.Program V In Out :=
  .seq (execute C P) (.local fun _ _ st => st.1)

theorem rounds {In Out : Type} (P : BroadcastModel.Program V In Out) :
    (translate P).rounds = P.rounds := by
  induction P with
  | «local» f => rfl
  | broadcast b C R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

theorem maxBits {In Out : Type} (P : BroadcastModel.Program V In Out) :
    (translate P).maxBits = P.maxBits := by
  induction P with
  | «local» f => rfl
  | broadcast b C R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ max ihP ihQ

theorem execute_rounds {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) : (execute C P).rounds = 1 + P.rounds := by
  change (PortDiscovery.prepare (In := In) C).rounds + (translate P).rounds = _
  rw [PortDiscovery.rounds, rounds]

theorem execute_maxBits {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) : (execute C P).maxBits = max b P.maxBits := by
  change max (PortDiscovery.prepare (In := In) C).maxBits (translate P).maxBits = _
  rw [PortDiscovery.maxBits, maxBits]

theorem program_rounds {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) : (program C P).rounds = 1 + P.rounds := by
  change (execute C P).rounds + 0 = _
  rw [execute_rounds, add_zero]

theorem program_maxBits {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) : (program C P).maxBits = max b P.maxBits := by
  change max (execute C P).maxBits 0 = _
  rw [execute_maxBits, Nat.max_zero]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem round_correct {In Out Msg : Type} {b : ℕ} (C : BroadcastModel.BitCode Msg b)
    (R : BroadcastModel.Round V In Out Msg) (ports : PortBroadcastModel.Numbering G)
    (s : V → In) (v : V) :
    (simulateRound C R).run G ports (fun u => (s u, PortDiscovery.learned G ports u)) v =
      (BroadcastModel.eval G R s v, PortDiscovery.learned G ports v) := by
  change (R.update v (PortDiscovery.neighbors (PortDiscovery.learned G ports v)) (s v)
    (fun u => PortDiscovery.read (PortDiscovery.learned G ports v) (G.degree v)
      (fun i => R.send (ports v i).val (PortDiscovery.neighbors (PortDiscovery.learned G ports (ports v i).val))
        (s (ports v i).val))
      (R.send v (PortDiscovery.neighbors (PortDiscovery.learned G ports v)) (s v)) u.val), _) = _
  rw [PortDiscovery.neighbors_correct G ports v]
  simp only [PortDiscovery.neighbors_correct]
  congr 1
  apply congrArg (R.update v (G.neighborFinset v) (s v))
  funext u
  exact PortDiscovery.read_correct G ports v (fun w => R.send w (G.neighborFinset w) (s w)) _ u

theorem translate_correct {In Out : Type} (P : BroadcastModel.Program V In Out)
    (ports : PortBroadcastModel.Numbering G) : ∀ s : V → In,
    (translate P).run G ports (fun v => (s v, PortDiscovery.learned G ports v)) =
      fun v => (P.run G s v, PortDiscovery.learned G ports v) := by
  induction P with
  | «local» f =>
    intro s
    funext v
    change (f v (PortDiscovery.neighbors (PortDiscovery.learned G ports v)) (s v), _) = _
    rw [PortDiscovery.neighbors_correct]
    rfl
  | broadcast b C R => intro s; funext v; exact round_correct G C R ports s v
  | seq P Q ihP ihQ =>
    intro s
    change (translate Q).run G ports ((translate P).run G ports
      (fun v => (s v, PortDiscovery.learned G ports v))) = _
    rw [ihP s]
    exact ihQ _

theorem execute_correct {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) (ports : PortBroadcastModel.Numbering G) (s : V → In) :
    (execute C P).run G ports s = fun v => (P.run G s v, PortDiscovery.learned G ports v) := by
  change (translate P).run G ports ((PortDiscovery.prepare C).run G ports s) = _
  rw [PortDiscovery.prepare_correct]
  exact translate_correct G P ports s

theorem execute_encoded_correct {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) (ports : PortBroadcastModel.Numbering G) (s : V → In) :
    (execute C P).runEncoded G ports s =
      fun v => (P.runEncoded G s v, PortDiscovery.learned G ports v) := by
  rw [PortBroadcastModel.Program.runEncoded_eq_run, BroadcastModel.Program.runEncoded_eq_run]
  exact execute_correct G C P ports s

theorem program_encoded_correct {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) (ports : PortBroadcastModel.Numbering G) (s : V → In) :
    (program C P).runEncoded G ports s = P.runEncoded G s := by
  change (fun v => ((execute C P).runEncoded G ports s v).1) = _
  rw [execute_encoded_correct]

theorem logarithmic_bits {In Out : Type} {b : ℕ} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V In Out) (n c K : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : P.maxBits ≤ K * Nat.clog 2 (n + 2)) :
    (program C P).maxBits ≤ max c K * Nat.clog 2 (n + 2) := by
  rw [program_maxBits]
  exact (max_le_max hids hmsg).trans_eq (by rw [max_mul_mul_right])

end Paper.KT0Compiler
