import Paper.Partitions.Local.DeterministicColorReductionPhysicalStep

/-! Actual varying-width color reduction on a physical network.
Every active scalar stage runs the received PhysicalStep; stopped stages are
local identities. Only public Delta, radius, identifier codec and bit widths
occur in the runtime. The graph power appears only in correctness statements.
Palette conversion and composition with the partition program remain separate. -/
namespace Paper.DeterministicColorReductionPhysicalProgram
open BroadcastModel DeterministicColorReductionArithmetic DeterministicColorReductionLogStar
open DeterministicColorReductionProgram
variable {V : Type} [LinearOrder V]

abbrev powerDegree (Δ r : ℕ) : ℕ := (Δ + 1) ^ r

def roundConstant (r c p d : ℕ) : ℕ :=
  r * DeterministicColorReductionIdentifiers.roundConstant c p d

def messageConstant (Δ r c p d : ℕ) : ℕ :=
  powerDegree Δ r * (2 * DeterministicColorReductionIdentifiers.bitFactor c p d + 1)

def program {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ) :
    (t b : ℕ) → Program V (Bits b) (Bits (run (powerDegree Δ r) t b))
  | 0, _ => .local fun _ _ s => s
  | t + 1, b =>
      if hb : b < threshold (powerDegree Δ r) then
        transport (small_width (powerDegree Δ r) t b hb) (.local fun _ _ s => s)
      else
        transport (active_width (powerDegree Δ r) t b hb)
          (.seq (DeterministicColorReductionPhysicalStep.program C Δ r b)
            (program C Δ r t (DeterministicColorReductionCodec.width b (powerDegree Δ r))))

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ r t b : ℕ) :
    (program C Δ r t b).rounds = r * usedRounds (powerDegree Δ r) t b := by
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
    by_cases hb : b < threshold (powerDegree Δ r)
    · simp only [program, dif_pos hb, transport_rounds, Program.rounds,
        usedRounds, if_pos hb, Nat.mul_zero]
    · simp only [program, dif_neg hb, transport_rounds, Program.rounds,
        DeterministicColorReductionPhysicalStep.rounds, ih, usedRounds, if_neg hb,
        Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem maxBits {ids : ℕ} (C : BitCode V ids) (Δ r t b : ℕ) :
    (program C Δ r t b).maxBits ≤ powerDegree Δ r * (ids + b + 1) := by
  induction t generalizing b with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    by_cases hb : b < threshold (powerDegree Δ r)
    · simpa only [program, dif_pos hb, transport_maxBits, Program.maxBits] using
        Nat.zero_le (powerDegree Δ r * (ids + b + 1))
    · have hf := active_width_le b (powerDegree Δ r) (by omega)
      have hm : powerDegree Δ r *
          (ids + DeterministicColorReductionCodec.width b (powerDegree Δ r) + 1) ≤
          powerDegree Δ r * (ids + b + 1) := Nat.mul_le_mul_left _ (by omega)
      simpa only [program, dif_neg hb, transport_maxBits, Program.maxBits] using
        max_le (DeterministicColorReductionPhysicalStep.maxBits C Δ r b)
          ((ih (DeterministicColorReductionCodec.width b (powerDegree Δ r))).trans hm)

/-- Only one's own identifier is used to initialize the proper input colors. -/
def fromIdentifiers {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ) :
    Program V Unit (Bits (run (powerDegree Δ r) (4 * logStar ids) ids)) :=
  .seq (.local fun v _ _ => C.encode v) (program C Δ r (4 * logStar ids) ids)

theorem identifiers_rounds {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ) :
    (fromIdentifiers C Δ r).rounds =
      r * (DeterministicColorReductionProgram.fromIdentifiers C (powerDegree Δ r)).rounds := by
  simp only [fromIdentifiers, DeterministicColorReductionProgram.fromIdentifiers,
    Program.rounds, Nat.zero_add, rounds, DeterministicColorReductionProgram.rounds]

theorem identifiers_maxBits {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ) :
    (fromIdentifiers C Δ r).maxBits ≤ powerDegree Δ r * (ids + ids + 1) := by
  simpa only [fromIdentifiers, Program.maxBits, Nat.zero_max] using
    maxBits C Δ r (4 * logStar ids) ids

section Order
variable [Fintype V]

/-- Public r,Delta,c,p,d determine both constants before the graph order. -/
theorem parameters {ids : ℕ} (C : BitCode V ids) (Δ r c p d M : ℕ)
    (hbits : ids ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (fromIdentifiers C Δ r).rounds ≤ roundConstant r c p d * (1 + logStar (Fintype.card V)) ∧
    (fromIdentifiers C Δ r).maxBits ≤ messageConstant Δ r c p d * Nat.clog 2 (Fintype.card V + 2) ∧
    run (powerDegree Δ r) (4 * logStar ids) ids < threshold (powerDegree Δ r) := by
  have ha := DeterministicColorReductionIdentifiers.parameters C (powerDegree Δ r) c p d M hbits hM
  have hb := DeterministicColorReductionIdentifiers.public_length_bound
    (Fintype.card V) ids c p d M hbits hM
  have hdouble : ids + ids ≤
      (2 * DeterministicColorReductionIdentifiers.bitFactor c p d) * Nat.clog 2 (Fintype.card V + 2) := by
    calc
      ids + ids ≤ DeterministicColorReductionIdentifiers.bitFactor c p d * Nat.clog 2 (Fintype.card V + 2) +
          DeterministicColorReductionIdentifiers.bitFactor c p d * Nat.clog 2 (Fintype.card V + 2) :=
        Nat.add_le_add hb hb
      _ = _ := by ring
  have hp := (BroadcastModel.logarithmic_message_budget (Fintype.card V) (ids + ids)
    (2 * DeterministicColorReductionIdentifiers.bitFactor c p d) hdouble).1
  constructor
  · rw [identifiers_rounds]
    calc
      _ ≤ r * (DeterministicColorReductionIdentifiers.roundConstant c p d *
          (1 + logStar (Fintype.card V))) := Nat.mul_le_mul_left r ha.1
      _ = _ := by unfold roundConstant; ring
  · constructor
    · calc
        _ ≤ powerDegree Δ r * (ids + ids + 1) := identifiers_maxBits C Δ r
        _ ≤ powerDegree Δ r *
            ((2 * DeterministicColorReductionIdentifiers.bitFactor c p d + 1) *
              Nat.clog 2 (Fintype.card V + 2)) := Nat.mul_le_mul_left _ hp
        _ = _ := by unfold messageConstant; ring
    · exact ha.2.2

theorem messages_logn {ids : ℕ} (C : BitCode V ids) (Δ r c p d M : ℕ)
    (hn : 2 ≤ Fintype.card V) (hbits : ids ≤ c * Nat.clog 2 M)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (fromIdentifiers C Δ r).maxBits ≤ (2 * messageConstant Δ r c p d) * Nat.clog 2 (Fintype.card V) := by
  calc
    _ ≤ messageConstant Δ r c p d * Nat.clog 2 (Fintype.card V + 2) :=
      (parameters C Δ r c p d M hbits hM).2.1
    _ ≤ messageConstant Δ r c p d * (2 * Nat.clog 2 (Fintype.card V)) :=
      Nat.mul_le_mul_left _ (DeterministicColorReductionIdentifiers.clog_shift_le _ hn)
    _ = _ := by ring

theorem parameters_small {ids : ℕ} (C : BitCode V ids) (Δ r c p d M : ℕ)
    (hn : Fintype.card V ≤ 1) (hbits : ids ≤ c * Nat.clog 2 M)
    (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (fromIdentifiers C Δ r).rounds ≤ roundConstant r c p d ∧
    (fromIdentifiers C Δ r).maxBits ≤ messageConstant Δ r c p d * 2 := by
  have h := parameters C Δ r c p d M hbits hM
  have hl : Nat.clog 2 (Fintype.card V + 2) ≤ 2 :=
    Nat.clog_le_of_le_pow (by norm_num; omega)
  constructor
  · simpa only [logStar_small (Fintype.card V) hn, Nat.add_zero, Nat.mul_one] using h.1
  · exact h.2.1.trans (Nat.mul_le_mul_left _ hl)

theorem numeric_parameters {M : ℕ} (D : DeterministicColorReductionIdentifiers.IdentifierRep V M)
    (Δ r p d : ℕ) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (fromIdentifiers (DeterministicColorReductionIdentifiers.identifierCode D) Δ r).rounds ≤
        roundConstant r 2 p d * (1 + logStar (Fintype.card V)) ∧
    (fromIdentifiers (DeterministicColorReductionIdentifiers.identifierCode D) Δ r).maxBits ≤
        messageConstant Δ r 2 p d * Nat.clog 2 (Fintype.card V + 2) ∧
    run (powerDegree Δ r) (4 * logStar (2 * Nat.clog 2 M)) (2 * Nat.clog 2 M) <
      threshold (powerDegree Δ r) :=
  parameters (DeterministicColorReductionIdentifiers.identifierCode D) Δ r 2 p d M le_rfl hM

end Order

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {ids : ℕ} (C : BitCode V ids) (Δ r t b : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    ∀ c : V → Bits b, (program C Δ r t b).runEncoded G c =
      colors (fun v => (DeterministicColorReductionPhysicalStep.power G r).neighborFinset v)
        (powerDegree Δ r) t b c := by
  induction t generalizing b with
  | zero => intro c; rfl
  | succ t ih =>
    intro c
    by_cases hb : b < threshold (powerDegree Δ r)
    · simpa only [program, colors, dif_pos hb] using
        transport_run G (small_width (powerDegree Δ r) t b hb) (.local fun _ _ s => s) c
    · have hc : (DeterministicColorReductionPhysicalStep.program C Δ r b).runEncoded G c =
          DeterministicColorReductionCodec.nextColor b (powerDegree Δ r)
            (fun v => (DeterministicColorReductionPhysicalStep.power G r).neighborFinset v) c :=
        funext (fun v => DeterministicColorReductionPhysicalStep.correct G C Δ r b c hdeg v)
      have hi := ih (DeterministicColorReductionCodec.width b (powerDegree Δ r))
        ((DeterministicColorReductionPhysicalStep.program C Δ r b).runEncoded G c)
      have hh : (Program.seq (DeterministicColorReductionPhysicalStep.program C Δ r b)
          (program C Δ r t (DeterministicColorReductionCodec.width b (powerDegree Δ r)))).runEncoded G c =
          colors (fun v => (DeterministicColorReductionPhysicalStep.power G r).neighborFinset v)
            (powerDegree Δ r) t (DeterministicColorReductionCodec.width b (powerDegree Δ r))
            (DeterministicColorReductionCodec.nextColor b (powerDegree Δ r)
              (fun v => (DeterministicColorReductionPhysicalStep.power G r).neighborFinset v) c) := by
        change (program C Δ r t (DeterministicColorReductionCodec.width b (powerDegree Δ r))).runEncoded G
          ((DeterministicColorReductionPhysicalStep.program C Δ r b).runEncoded G c) = _
        rw [hi, hc]
      have hhcast := congrArg (fun f : V → Bits
          (run (powerDegree Δ r) t (DeterministicColorReductionCodec.width b (powerDegree Δ r))) =>
        fun v => castBits (active_width (powerDegree Δ r) t b hb) (f v)) hh
      simpa only [program, colors, dif_neg hb] using
        (transport_run G (active_width (powerDegree Δ r) t b hb)
          (.seq (DeterministicColorReductionPhysicalStep.program C Δ r b)
            (program C Δ r t (DeterministicColorReductionCodec.width b (powerDegree Δ r)))) c).trans hhcast

theorem correct_power_program {ids : ℕ} (C : BitCode V ids) (Δ r t b : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (c : V → Bits b) :
    (program C Δ r t b).runEncoded G c =
      (DeterministicColorReductionProgram.program (powerDegree Δ r) t b).runEncoded
        (DeterministicColorReductionPhysicalStep.power G r) c := by
  rw [correct G C Δ r t b hdeg, DeterministicColorReductionProgram.correct]

theorem proper {ids : ℕ} (C : BitCode V ids) (Δ r t b : ℕ) (c : V → Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hc : ∀ u v, (DeterministicColorReductionPhysicalStep.power G r).Adj u v → c u ≠ c v)
    (u v : V) (ha : (DeterministicColorReductionPhysicalStep.power G r).Adj u v) :
    (program C Δ r t b).runEncoded G c u ≠ (program C Δ r t b).runEncoded G c v := by
  rw [correct G C Δ r t b hdeg]
  exact colors_proper (DeterministicColorReductionPhysicalStep.power G r) (powerDegree Δ r) t b
    (DeterministicColorReductionPhysicalStep.power_degree_bound G Δ r hdeg) c hc u v ha

theorem identifiers_output {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) :
    (fromIdentifiers C Δ r).runEncoded G (fun _ => ()) =
      colors (fun v => (DeterministicColorReductionPhysicalStep.power G r).neighborFinset v)
        (powerDegree Δ r) (4 * logStar ids) ids C.encode := by
  change (program C Δ r (4 * logStar ids) ids).runEncoded G C.encode = _
  exact correct G C Δ r _ _ hdeg _

theorem identifiers_proper {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u v : V)
    (ha : (DeterministicColorReductionPhysicalStep.power G r).Adj u v) :
    (fromIdentifiers C Δ r).runEncoded G (fun _ => ()) u ≠
      (fromIdentifiers C Δ r).runEncoded G (fun _ => ()) v := by
  change (program C Δ r (4 * logStar ids) ids).runEncoded G C.encode u ≠
    (program C Δ r (4 * logStar ids) ids).runEncoded G C.encode v
  exact proper G C Δ r _ _ C.encode hdeg
    (fun u v ha => DeterministicColorReductionStep.identifiers_proper
      (DeterministicColorReductionPhysicalStep.power G r) C u v ha) u v ha

/-- The near-vertex form required by the received partition's hpower contract. -/
theorem identifiers_proper_ball {ids : ℕ} (C : BitCode V ids) (Δ r : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u v : V) (hne : u ≠ v)
    (hball : v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u r) :
    (fromIdentifiers C Δ r).runEncoded G (fun _ => ()) u ≠
      (fromIdentifiers C Δ r).runEncoded G (fun _ => ()) v :=
  identifiers_proper G C Δ r hdeg u v ⟨hne, hball⟩

end Graph
end Paper.DeterministicColorReductionPhysicalProgram

#print axioms Paper.DeterministicColorReductionPhysicalProgram.correct
#print axioms Paper.DeterministicColorReductionPhysicalProgram.correct_power_program
#print axioms Paper.DeterministicColorReductionPhysicalProgram.rounds
#print axioms Paper.DeterministicColorReductionPhysicalProgram.maxBits
#print axioms Paper.DeterministicColorReductionPhysicalProgram.identifiers_output
#print axioms Paper.DeterministicColorReductionPhysicalProgram.identifiers_proper_ball
#print axioms Paper.DeterministicColorReductionPhysicalProgram.parameters
#print axioms Paper.DeterministicColorReductionPhysicalProgram.numeric_parameters
