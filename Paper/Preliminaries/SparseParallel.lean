import Paper.Preliminaries.SparseRolePrepare
import Paper.Communication.ProgramMemory

/-! Actual keyed sparse parallel BC compiler. Every physical sender sends
one bounded list of role/message pairs to all its neighbors. -/
namespace Paper.SparseParallel
open BroadcastModel
variable {V R : Type} [DecidableEq V] [LinearOrder R]

def messages {In Out Msg : Type} (round : Round V In Out Msg) (v : V)
    (env : SparseRolePrepare.Env V R) (xs : List (R × In)) : List (R × Msg) :=
  RoleDictionary.mapValues (fun r s => round.send v (env.neighbors r) s) xs

def updates {In Out Msg : Type} {K : ℕ} (round : Round V In Out Msg) (v : V) (N : Finset V)
    (env : SparseRolePrepare.Env V R) (xs : List (R × In))
    (incoming : N → {l : List (R × Msg) // l.length ≤ K}) : List (R × Out) :=
  RoleDictionary.mapValues (fun r s => round.update v (N ∩ env.neighbors r) s
    (fun u => (TaggedDictionary.lookup (incoming ⟨u.val, (Finset.mem_inter.mp u.property).1⟩).val r).getD
      (round.send v (env.neighbors r) s))) xs

def simulateRound {In Out Msg : Type} {b w : ℕ} (C : BitCode R b) (P : BitCode Msg w) (K : ℕ)
    (round : Round V In Out Msg) :
    Program V (List (R × In) × SparseRolePrepare.Env V R) (List (R × Out) × SparseRolePrepare.Env V R) :=
  .broadcast (K * (b + w + 1)) (ListPacket.bounded (PacketCode.product C P) K) {
    send := fun v _ s => TaggedDictionary.bounded K (messages round v s.2 s.1)
    update := fun v N s incoming => (updates round v N s.2 s.1 incoming, s.2) }

def translate {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} :
    Program V In Out → Program V (List (R × In) × SparseRolePrepare.Env V R)
      (List (R × Out) × SparseRolePrepare.Env V R)
  | .local f => .local fun v _ s => (RoleDictionary.mapValues (fun r x => f v (s.2.neighbors r) x) s.1, s.2)
  | .broadcast _ P round => simulateRound C P K round
  | .seq P Q => .seq (translate C K P) (translate C K Q)

def execute {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out) :
    Program V (List (R × In)) (List (R × Out) × SparseRolePrepare.Env V R) :=
  .seq (.local fun _ _ xs => (TaggedDictionary.keys xs, xs))
    (.seq (ProgramMemory.carry (SparseRolePrepare.program C K))
      (.seq (.local fun _ _ s => (s.2, s.1)) (translate C K P)))

theorem rounds {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate C K P).rounds = P.rounds := by
  induction P with
  | «local» _ => rfl
  | broadcast _ _ _ => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

theorem maxBits {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate C K P).maxBits ≤ K * (b + P.maxBits + 1) := by
  induction P with
  | «local» _ => exact Nat.zero_le _
  | broadcast _ _ _ => exact le_refl _
  | seq P Q ihP ihQ =>
    apply max_le
    · exact ihP.trans (Nat.mul_le_mul_left K (by change b + P.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))
    · exact ihQ.trans (Nat.mul_le_mul_left K (by change b + Q.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))

theorem execute_rounds {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute C K P).rounds = 1 + P.rounds := by
  simp only [execute, Program.rounds, ProgramMemory.rounds, SparseRolePrepare.rounds, rounds, Nat.zero_add]

theorem execute_maxBits {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute C K P).maxBits ≤ K * (b + P.maxBits + 1) := by
  simp only [execute, Program.maxBits, ProgramMemory.maxBits, SparseRolePrepare.maxBits, Nat.zero_max]
  exact max_le (Nat.mul_le_mul_left K (by omega)) (maxBits C K P)

theorem logarithmic_bits {b : ℕ} (C : BitCode R b) (K : ℕ) {In Out : Type} (P : Program V In Out)
    (n c d : ℕ) (hrole : b ≤ c * Nat.clog 2 (n + 2))
    (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (execute C K P).maxBits ≤ (K * (c + d + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  apply (execute_maxBits C K P).trans
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith
end Paper.SparseParallel
