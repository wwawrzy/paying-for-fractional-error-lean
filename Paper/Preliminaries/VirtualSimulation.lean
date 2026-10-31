import Paper.Owners.Construction.OwnerVirtualPrepare

/-! Literal graph-independent compiler from virtual broadcast programs to
physical programs using the actual owner router. Private Env is preserved;
no public decoder, Inhabited payload or virtual-neighbor oracle is needed
by construction. Correctness uses the actual prepared Env separately. -/
namespace Paper.VirtualSimulation
open BroadcastModel
variable {V : Type} [LinearOrder V]

def prepare {In Out Msg : Type} (R : Round V In Out Msg) :
    Program V (In × OwnerVirtualPrepare.Env V)
      (OwnerPayloadRoute.Input V Msg × ((In × OwnerVirtualPrepare.Env V) × Msg)) :=
  .local fun v _ s =>
    let msg := R.send v s.2.neighbors s.1
    (⟨s.2.metadata, s.2.low, msg⟩, (s, msg))

def finish {In Out Msg : Type} (R : Round V In Out Msg) :
    Program V (List (V × Msg) × ((In × OwnerVirtualPrepare.Env V) × Msg)) (Out × OwnerVirtualPrepare.Env V) :=
  .local fun v _ s =>
    let saved := s.2.1
    (R.update v saved.2.neighbors saved.1 (fun u => (TaggedDictionary.lookup s.1 u.val).getD s.2.2), saved.2)

def simulateRound {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (L Δ : ℕ) (R : Round V In Out Msg) : Program V (In × OwnerVirtualPrepare.Env V) (Out × OwnerVirtualPrepare.Env V) :=
  .seq (prepare R) (.seq (ProgramMemory.carry (OwnerPayloadRoute.program C P L Δ)) (finish R))

def translate {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} :
    Program V In Out → Program V (In × OwnerVirtualPrepare.Env V) (Out × OwnerVirtualPrepare.Env V)
  | .local f => .local fun v _ s => (f v s.2.neighbors s.1, s.2)
  | .broadcast _ P R => simulateRound C P L Δ R
  | .seq P Q => .seq (translate C L Δ P) (translate C L Δ Q)

def execute {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    Program V ((Bool × Bool) × In) (Out × OwnerVirtualPrepare.Env V) :=
  .seq (ProgramMemory.carry (OwnerVirtualPrepare.program C L Δ))
    (.seq (.local fun _ _ s => (s.2, s.1)) (translate C L Δ P))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem round_run {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (L Δ : ℕ) (R : Round V In Out Msg) (s : V → In × OwnerVirtualPrepare.Env V) :
    (simulateRound C P L Δ R).run G s =
      let msg := fun v => R.send v (s v).2.neighbors (s v).1
      let inputs := fun v => (⟨(s v).2.metadata, (s v).2.low, msg v⟩ : OwnerPayloadRoute.Input V Msg)
      let data := (OwnerPayloadRoute.program C P L Δ).run G inputs
      fun v => (R.update v (s v).2.neighbors (s v).1 (fun u => (TaggedDictionary.lookup (data v) u.val).getD (msg v)), (s v).2) := by
  change (finish R).run G ((ProgramMemory.carry (OwnerPayloadRoute.program C P L Δ)).run G
    (fun v => ((⟨(s v).2.metadata, (s v).2.low, R.send v (s v).2.neighbors (s v).1⟩ : OwnerPayloadRoute.Input V Msg),
      (s v, R.send v (s v).2.neighbors (s v).1)))) = _
  rw [ProgramMemory.run G (OwnerPayloadRoute.program C P L Δ)]
  rfl

theorem round_env {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (L Δ : ℕ) (R : Round V In Out Msg) (s : V → In × OwnerVirtualPrepare.Env V) (v : V) :
    ((simulateRound C P L Δ R).run G s v).2 = (s v).2 := by
  rw [round_run]

theorem env_preserved {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    ∀ s : V → In × OwnerVirtualPrepare.Env V, ∀ v, ((translate C L Δ P).run G s v).2 = (s v).2 := by
  induction P with
  | «local» f => intro s v; rfl
  | broadcast w code R => intro s v; exact round_env G C code L Δ R s v
  | seq P Q ihP ihQ =>
    intro s v
    exact (ihQ ((translate C L Δ P).run G s) v).trans (ihP s v)

theorem round_rounds {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (L Δ : ℕ) (R : Round V In Out Msg) : (simulateRound C P L Δ R).rounds = 4 := rfl

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate C L Δ P).rounds = 4 * P.rounds := by
  induction P with
  | «local» f => rfl
  | broadcast w code R => rfl
  | seq P Q ihP ihQ => simp only [translate, Program.rounds, ihP, ihQ, Nat.mul_add]

theorem round_maxBits {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (L Δ : ℕ) (R : Round V In Out Msg) :
    (simulateRound C P L Δ R).maxBits ≤ (L + Δ + 3) * (b + w + 1) := by
  simp only [simulateRound, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact OwnerPayloadRoute.maxBits C P L Δ

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate C L Δ P).maxBits ≤ (L + Δ + 3) * (b + P.maxBits + 1) := by
  induction P with
  | «local» f => exact Nat.zero_le _
  | broadcast w code R => exact round_maxBits C code L Δ R
  | seq P Q ihP ihQ =>
    apply max_le
    · exact ihP.trans (Nat.mul_le_mul_left _ (by change b + P.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))
    · exact ihQ.trans (Nat.mul_le_mul_left _ (by change b + Q.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (n c d : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (translate C L Δ P).maxBits ≤ ((L + Δ + 3) * (c + d + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + P.maxBits + 1 ≤ (c + d + 1) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits C L Δ P).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

theorem execute_rounds {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute C L Δ P).rounds = 10 + 4 * P.rounds := by
  simp only [execute, Program.rounds, ProgramMemory.rounds, OwnerVirtualPrepare.rounds, rounds, Nat.zero_add]

theorem execute_maxBits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute C L Δ P).maxBits ≤ (L + Δ + 4) * (b + P.maxBits + 2) := by
  simp only [execute, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]
  apply max_le
  · exact (OwnerVirtualPrepare.maxBits C L Δ).trans (by nlinarith)
  · exact (maxBits C L Δ P).trans (by nlinarith)

theorem execute_logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (n c d : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (execute C L Δ P).maxBits ≤ ((L + Δ + 4) * (c + d + 2)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + P.maxBits + 2 ≤ (c + d + 2) * Nat.clog 2 (n + 2) := by nlinarith
  apply (execute_maxBits C L Δ P).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 4) hb
end Paper.VirtualSimulation
