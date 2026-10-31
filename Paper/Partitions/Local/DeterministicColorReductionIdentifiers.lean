import Paper.Partitions.Local.DeterministicColorReductionProgram

/-! Convert the public polynomial identifier convention to graph-order bounds.
The common capacity M contains the numerical identifiers as values < M.
The encoding factor c and polynomial constants p,d are fixed before the graph;
only the proof uses M <= p*(n+2)^d. Runtime needs the public identifier code,
its bit width, and Delta, not n. No proper coloring is supplied as an input.
Physical simulation on a graph power and the partition endpoint remain separate. -/
namespace Paper.DeterministicColorReductionIdentifiers
open BroadcastModel DeterministicColorReductionArithmetic DeterministicColorReductionLogStar

def bitFactor (c p d : ℕ) : ℕ := c * (p + d)

def roundConstant (c p d : ℕ) : ℕ := 4 * (bitFactor c p d + 2)

theorem double_le_two_pow (x : ℕ) : 2 * x ≤ 2 ^ x := by
  cases x with
  | zero => norm_num
  | succ x =>
    rw [Nat.pow_succ]
    have hp : x < 2 ^ x := Nat.lt_pow_self (by decide : 1 < 2)
    omega

theorem logStar_pow (x : ℕ) : logStar (2 ^ x) ≤ logStar x + 1 := by
  by_cases hx : x = 0
  · subst x
    rw [Nat.pow_zero, logStar_small 1 (by decide), logStar_small 0 (by decide)]
    omega
  · have hp : 1 < 2 ^ x := Nat.one_lt_pow hx (by decide : 1 < 2)
    rw [logStar_step (2 ^ x) hp, Nat.clog_pow 2 x (by decide : 1 < 2)]

theorem logStar_double (x : ℕ) : logStar (2 * x) ≤ logStar x + 1 :=
  (logStar_mono (double_le_two_pow x)).trans (logStar_pow x)

/-- An economical constant-factor bound derived from genuine logStar properties. -/
theorem logStar_mul_bound (k x : ℕ) : logStar (k * x) ≤ k + logStar x := by
  induction k with
  | zero =>
    simpa only [Nat.zero_mul, Nat.zero_add, logStar_small 0 (by decide)] using
      Nat.zero_le (logStar x)
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simpa only [Nat.zero_add, Nat.one_mul] using (show logStar x ≤ 1 + logStar x by omega)
    · have hp : (k + 1) * x ≤ 2 * (k * x) := by
        calc
          (k + 1) * x ≤ (2 * k) * x := Nat.mul_le_mul_right x (by omega)
          _ = _ := by ring
      calc
        logStar ((k + 1) * x) ≤ logStar (2 * (k * x)) := logStar_mono hp
        _ ≤ logStar (k * x) + 1 := logStar_double _
        _ ≤ (k + 1) + logStar x := by omega

theorem logStar_succ (n : ℕ) : logStar (n + 1) ≤ logStar n + 1 := by
  have hp : n + 1 ≤ 2 ^ n := by
    have h : n < 2 ^ n := Nat.lt_pow_self (by decide : 1 < 2)
    omega
  exact (logStar_mono hp).trans (logStar_pow n)

theorem logStar_clog_shift (n : ℕ) : logStar (Nat.clog 2 (n + 2)) ≤ logStar n + 1 := by
  have hrec : logStar (n + 2) = logStar (Nat.clog 2 (n + 2)) + 1 :=
    logStar_step (n + 2) (by omega)
  have h1 := logStar_succ n
  have h2 := logStar_succ (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at h2
  omega

theorem logStar_bits_bound (n b k : ℕ) (hb : b ≤ k * Nat.clog 2 (n + 2)) :
    logStar b ≤ k + logStar n + 1 := by
  calc
    logStar b ≤ logStar (k * Nat.clog 2 (n + 2)) := logStar_mono hb
    _ ≤ k + logStar (Nat.clog 2 (n + 2)) := logStar_mul_bound _ _
    _ ≤ k + logStar n + 1 := Nat.add_le_add_left (logStar_clog_shift n) k

theorem round_budget_bound (n b k : ℕ) (hb : b ≤ k * Nat.clog 2 (n + 2)) :
    4 * logStar b ≤ 4 * (k + 2) * (1 + logStar n) := by
  have hs := logStar_bits_bound n b k hb
  nlinarith [Nat.zero_le (k * logStar n)]

/-- Absorb a polynomial coefficient p into the fixed exponent p+d. -/
theorem public_log_bound (n M p d : ℕ) (hM : M ≤ p * (n + 2) ^ d) :
    Nat.clog 2 M ≤ (p + d) * Nat.clog 2 (n + 2) := by
  have hp : p ≤ (n + 2) ^ p :=
    (self_le_two_pow p).trans (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) p)
  have hn := Nat.le_pow_clog (by decide : 1 < 2) (n + 2)
  apply Nat.clog_le_of_le_pow
  calc
    M ≤ p * (n + 2) ^ d := hM
    _ ≤ (n + 2) ^ p * (n + 2) ^ d := Nat.mul_le_mul_right _ hp
    _ = (n + 2) ^ (p + d) := by rw [Nat.pow_add]
    _ ≤ (2 ^ Nat.clog 2 (n + 2)) ^ (p + d) := Nat.pow_le_pow_left hn _
    _ = 2 ^ ((p + d) * Nat.clog 2 (n + 2)) := by
      rw [← Nat.pow_mul]
      congr 1
      ring

theorem public_length_bound (n b c p d M : ℕ)
    (hbits : b ≤ c * Nat.clog 2 M) (hM : M ≤ p * (n + 2) ^ d) :
    b ≤ bitFactor c p d * Nat.clog 2 (n + 2) := by
  calc
    b ≤ c * Nat.clog 2 M := hbits
    _ ≤ c * ((p + d) * Nat.clog 2 (n + 2)) :=
      Nat.mul_le_mul_left c (public_log_bound n M p d hM)
    _ = _ := by unfold bitFactor; ring

theorem clog_shift_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n + 2) ≤ 2 * Nat.clog 2 n := by
  have hsmall : n + 2 ≤ n * n := by
    have hp := Nat.mul_le_mul_left n hn
    omega
  have hp := Nat.le_pow_clog (by decide : 1 < 2) n
  apply Nat.clog_le_of_le_pow
  calc
    n + 2 ≤ n * n := hsmall
    _ ≤ 2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n := Nat.mul_le_mul hp hp
    _ = 2 ^ (2 * Nat.clog 2 n) := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-- Public numerical identifier representation, with its local partial decoder.
The inverse law provides uniqueness; no graph enumeration or choice is used. -/
structure IdentifierRep (V : Type) (M : ℕ) where
  value : V → Fin M
  read : Fin M → Option V
  leftInverse : ∀ v, read (value v) = some v

variable {V : Type}

def identifierCode {M : ℕ} (D : IdentifierRep V M) : BitCode V (2 * Nat.clog 2 M) :=
  PacketCode.ofInverse
    (fun v => (DeterministicColorReductionCodec.numberCode M).encode (D.value v))
    (fun bits => ((DeterministicColorReductionCodec.numberCode M).decode bits).bind D.read)
    (by
      intro v
      dsimp only
      rw [(DeterministicColorReductionCodec.numberCode M).leftInverse]
      simp only [Option.bind_some]
      exact D.leftInverse v)

variable [DecidableEq V]

def numericProgram {M : ℕ} (D : IdentifierRep V M) (Δ : ℕ) :
    Program V Unit (DeterministicColorReductionProgram.Bits
      (run Δ (4 * logStar (2 * Nat.clog 2 M)) (2 * Nat.clog 2 M))) :=
  DeterministicColorReductionProgram.fromIdentifiers (identifierCode D) Δ

section Order
variable [Fintype V]

/-- Constants c,p,d and the coefficients above are graph-independent.
M and its encoding length are public; the graph order appears only in this proof. -/
theorem parameters {b : ℕ} (C : BitCode V b) (Δ c p d M : ℕ)
    (hbits : b ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).rounds ≤
        roundConstant c p d * (1 + logStar (Fintype.card V)) ∧
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).maxBits ≤
        bitFactor c p d * Nat.clog 2 (Fintype.card V + 2) ∧
    run Δ (4 * logStar b) b < threshold Δ := by
  have hb := public_length_bound (Fintype.card V) b c p d M hbits hM
  constructor
  · exact (DeterministicColorReductionProgram.identifiers_rounds C Δ).trans
      (round_budget_bound (Fintype.card V) b (bitFactor c p d) hb)
  · exact ⟨(DeterministicColorReductionProgram.identifiers_maxBits C Δ).trans hb,
      schedule_small b Δ⟩

theorem parameters_zero {b : ℕ} (C : BitCode V b) (Δ c p d M : ℕ)
    (hn : Fintype.card V = 0) (hbits : b ≤ c * Nat.clog 2 M)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).rounds ≤ roundConstant c p d ∧
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).maxBits ≤ bitFactor c p d := by
  have h := parameters C Δ c p d M hbits hM
  constructor
  · simpa only [hn, logStar_small 0 (by decide), Nat.add_zero, Nat.mul_one] using h.1
  · simpa only [hn, show Nat.clog 2 (0 + 2) = 1 by decide, Nat.mul_one] using h.2.1

theorem parameters_one {b : ℕ} (C : BitCode V b) (Δ c p d M : ℕ)
    (hn : Fintype.card V = 1) (hbits : b ≤ c * Nat.clog 2 M)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).rounds ≤ roundConstant c p d ∧
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).maxBits ≤ bitFactor c p d * 2 := by
  have h := parameters C Δ c p d M hbits hM
  constructor
  · simpa only [hn, logStar_small 1 (by decide), Nat.add_zero, Nat.mul_one] using h.1
  · simpa only [hn, show Nat.clog 2 (1 + 2) = 2 by decide] using h.2.1

theorem messages_logn {b : ℕ} (C : BitCode V b) (Δ c p d M : ℕ)
    (hn : 2 ≤ Fintype.card V) (hbits : b ≤ c * Nat.clog 2 M)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (DeterministicColorReductionProgram.fromIdentifiers C Δ).maxBits ≤
      (2 * bitFactor c p d) * Nat.clog 2 (Fintype.card V) := by
  calc
    _ ≤ bitFactor c p d * Nat.clog 2 (Fintype.card V + 2) :=
      (parameters C Δ c p d M hbits hM).2.1
    _ ≤ bitFactor c p d * (2 * Nat.clog 2 (Fintype.card V)) :=
      Nat.mul_le_mul_left _ (clog_shift_le _ hn)
    _ = _ := by ring

theorem numeric_parameters {M : ℕ} (D : IdentifierRep V M) (Δ p d : ℕ)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (numericProgram D Δ).rounds ≤ roundConstant 2 p d * (1 + logStar (Fintype.card V)) ∧
    (numericProgram D Δ).maxBits ≤ bitFactor 2 p d * Nat.clog 2 (Fintype.card V + 2) ∧
    run Δ (4 * logStar (2 * Nat.clog 2 M)) (2 * Nat.clog 2 M) < threshold Δ :=
  parameters (identifierCode D) Δ 2 p d M le_rfl hM

end Order

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem numeric_output {M : ℕ} (D : IdentifierRep V M) (Δ : ℕ) :
    (numericProgram D Δ).runEncoded G (fun _ => ()) =
      DeterministicColorReductionProgram.colors (fun v => G.neighborFinset v) Δ
        (4 * logStar (2 * Nat.clog 2 M)) (2 * Nat.clog 2 M) (identifierCode D).encode := by
  change (DeterministicColorReductionProgram.program Δ
    (4 * logStar (2 * Nat.clog 2 M)) (2 * Nat.clog 2 M)).runEncoded G (identifierCode D).encode = _
  exact DeterministicColorReductionProgram.correct G Δ _ _ _

theorem numeric_proper {M : ℕ} (D : IdentifierRep V M) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u v : V) (ha : G.Adj u v) :
    (numericProgram D Δ).runEncoded G (fun _ => ()) u ≠
      (numericProgram D Δ).runEncoded G (fun _ => ()) v :=
  DeterministicColorReductionProgram.identifiers_proper G (identifierCode D) Δ hdeg u v ha

end Graph
end Paper.DeterministicColorReductionIdentifiers

#print axioms Paper.DeterministicColorReductionIdentifiers.logStar_mul_bound
#print axioms Paper.DeterministicColorReductionIdentifiers.logStar_bits_bound
#print axioms Paper.DeterministicColorReductionIdentifiers.parameters
#print axioms Paper.DeterministicColorReductionIdentifiers.parameters_zero
#print axioms Paper.DeterministicColorReductionIdentifiers.parameters_one
#print axioms Paper.DeterministicColorReductionIdentifiers.messages_logn
#print axioms Paper.DeterministicColorReductionIdentifiers.numeric_parameters
#print axioms Paper.DeterministicColorReductionIdentifiers.numeric_output
#print axioms Paper.DeterministicColorReductionIdentifiers.numeric_proper
