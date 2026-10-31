import Paper.Partitions.Local.DeterministicColorReductionStep
import Paper.Preliminaries.BinaryCounter

/-! Explicit binary recoding of the canonical padded first-difference set.
Each padded symbol is represented in Fin(2*b+1), range-checked after binary
counter decoding. PacketCode.vector combines Delta slots. The set decoder
checks canonical padding. Oversized set inputs have a defined zero output.
No abstract finite enumeration or one-hot palette codec is used here. -/
namespace Paper.DeterministicColorReductionCodec
open BroadcastModel

abbrev SmallSet (b Δ : ℕ) := {S : Finset (DeterministicColorReductionStep.Pair b) // S.card ≤ Δ}

def width (b Δ : ℕ) : ℕ := Δ * (2 * Nat.clog 2 (2 * b + 1))

/-- Restrict the received explicit binary counter codec to values below m. -/
def numberCode (m : ℕ) : BitCode (Fin m) (2 * Nat.clog 2 m) :=
  PacketCode.ofInverse
    (fun i => (BinaryCounter.code (Nat.clog 2 m)).encode
      ⟨i.val, i.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) m)⟩)
    (fun bits => ((BinaryCounter.code (Nat.clog 2 m)).decode bits).bind (fun i =>
      if h : i.val < m then some ⟨i.val, h⟩ else none))
    (by
      intro i
      dsimp only
      rw [(BinaryCounter.code (Nat.clog 2 m)).leftInverse]
      simp only [Option.bind_some]
      rw [dif_pos i.isLt])

/-- Unused numeric counter values are rejected, including every value for m=0. -/
theorem numberCode_reject (m : ℕ) (i : Fin (2 ^ Nat.clog 2 m)) (hi : ¬ i.val < m) :
    (numberCode m).decode ((BinaryCounter.code (Nat.clog 2 m)).encode i) = none := by
  dsimp only [numberCode, PacketCode.ofInverse]
  rw [(BinaryCounter.code (Nat.clog 2 m)).leftInverse]
  simp only [Option.bind_some, dif_neg hi]

/-- none is ordinal zero; some i is its explicit successor ordinal. -/
def symbolCode (b : ℕ) : BitCode (Option (Fin (2 * b))) (2 * Nat.clog 2 (2 * b + 1)) :=
  PacketCode.transport (numberCode (2 * b + 1)) (finSuccEquiv' (0 : Fin (2 * b + 1)))

def wordCode (b Δ : ℕ) : BitCode (Fin Δ → Option (Fin (2 * b))) (width b Δ) :=
  PacketCode.vector (symbolCode b) Δ

/-- A total interpretation of any padded word; repetitions are deduplicated. -/
def fromWord (b Δ : ℕ) (w : Fin Δ → Option (Fin (2 * b))) : Finset (DeterministicColorReductionStep.Pair b) :=
  (ListPacket.unpack w).toFinset.image (DeterministicColorReductionStep.pairCode b).symm

theorem fromWord_size (b Δ : ℕ) (w : Fin Δ → Option (Fin (2 * b))) : (fromWord b Δ w).card ≤ Δ := by
  calc
    _ ≤ (ListPacket.unpack w).toFinset.card := Finset.card_image_le
    _ ≤ (ListPacket.unpack w).length := List.toFinset_card_le _
    _ ≤ Δ := ListPacket.unpack_length w

theorem fromWord_padded (b Δ : ℕ) (S : SmallSet b Δ) :
    fromWord b Δ (DeterministicColorReductionStep.padded b Δ S.val) = S.val := by
  have hlen : ((S.val.image (DeterministicColorReductionStep.pairCode b)).sort (· ≤ ·)).length ≤ Δ := by
    rw [Finset.length_sort, Finset.card_image_of_injective _
      (DeterministicColorReductionStep.pairCode b).injective]
    exact S.property
  unfold fromWord DeterministicColorReductionStep.padded
  rw [ListPacket.unpack_pack Δ _ hlen, Finset.sort_toFinset, Finset.image_image]
  simp only [Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']

/-- Reject words that are not exactly the canonical sorted padding. -/
def readWord (b Δ : ℕ) (w : Fin Δ → Option (Fin (2 * b))) : Option (SmallSet b Δ) :=
  let S := fromWord b Δ w
  if _h : DeterministicColorReductionStep.padded b Δ S = w then
    some ⟨S, fromWord_size b Δ w⟩ else none

theorem readWord_padded (b Δ : ℕ) (S : SmallSet b Δ) :
    readWord b Δ (DeterministicColorReductionStep.padded b Δ S.val) = some S := by
  have he := fromWord_padded b Δ S
  have hc := congrArg (DeterministicColorReductionStep.padded b Δ) he
  dsimp only [readWord]
  split_ifs with hcanon
  · exact congrArg some (Subtype.ext he)

theorem readWord_reject (b Δ : ℕ) (w : Fin Δ → Option (Fin (2 * b)))
    (h : DeterministicColorReductionStep.padded b Δ (fromWord b Δ w) ≠ w) :
    readWord b Δ w = none := by
  dsimp only [readWord]
  split_ifs with hcanon
  · exact False.elim (h hcanon)
  · rfl

/-- Binary codec of the actual bounded set, with explicit decoder and inverse. -/
def code (b Δ : ℕ) : BitCode (SmallSet b Δ) (width b Δ) :=
  PacketCode.ofInverse
    (fun S => (wordCode b Δ).encode (DeterministicColorReductionStep.padded b Δ S.val))
    (fun bits => ((wordCode b Δ).decode bits).bind (readWord b Δ))
    (by
      intro S
      dsimp only
      rw [(wordCode b Δ).leftInverse]
      simp only [Option.bind_some]
      exact readWord_padded b Δ S)

theorem decode_encode (b Δ : ℕ) (S : SmallSet b Δ) :
    (code b Δ).decode ((code b Δ).encode S) = some S := (code b Δ).leftInverse S

/-- Total runtime encoder. On an oversized input, emit the zero vector. -/
def encodeOutput (b Δ : ℕ) (S : Finset (DeterministicColorReductionStep.Pair b)) :
    DeterministicColorReductionStep.Bits (width b Δ) :=
  if h : S.card ≤ Δ then (code b Δ).encode ⟨S, h⟩ else fun _ => false

theorem encodeOutput_valid (b Δ : ℕ) (S : Finset (DeterministicColorReductionStep.Pair b)) (h : S.card ≤ Δ) :
    encodeOutput b Δ S = (code b Δ).encode ⟨S, h⟩ := by
  simp only [encodeOutput, dif_pos h]

theorem encodeOutput_outside (b Δ : ℕ) (S : Finset (DeterministicColorReductionStep.Pair b)) (h : ¬ S.card ≤ Δ) :
    encodeOutput b Δ S = (fun _ => false) := by
  simp only [encodeOutput, dif_neg h]

@[simp] theorem width_zero_bits (Δ : ℕ) : width 0 Δ = 0 := by simp [width]
@[simp] theorem width_zero_degree (b : ℕ) : width b 0 = 0 := by simp [width]

theorem encode_zero_bits (Δ : ℕ) (S : Finset (DeterministicColorReductionStep.Pair 0)) :
    encodeOutput 0 Δ S = (fun _ => false) := by
  funext i
  have hi := i.isLt
  have hz := width_zero_bits Δ
  omega

theorem encode_zero_degree (b : ℕ) (S : Finset (DeterministicColorReductionStep.Pair b)) :
    encodeOutput b 0 S = (fun _ => false) := by
  funext i
  have hi := i.isLt
  have hz := width_zero_degree b
  omega

theorem width_upper (b Δ : ℕ) : width b Δ ≤ 2 * Δ * (Nat.clog 2 (b + 1) + 1) := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (b + 1)
  have hl : Nat.clog 2 (2 * b + 1) ≤ Nat.clog 2 (b + 1) + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.pow_succ]
    omega
  calc
    width b Δ ≤ Δ * (2 * (Nat.clog 2 (b + 1) + 1)) :=
      Nat.mul_le_mul_left Δ (Nat.mul_le_mul_left 2 hl)
    _ = _ := by ring

/-- An explicit all-parameter logarithmic bound, including b=0 and Δ=0. -/
theorem width_logarithmic (b Δ : ℕ) : width b Δ ≤ 4 * Δ * Nat.clog 2 (b + 1) := by
  by_cases hb : b = 0
  · subst b
    simp
  · have hl : 0 < Nat.clog 2 (b + 1) := Nat.clog_pos (by decide) (by omega)
    calc
      width b Δ ≤ 2 * Δ * (Nat.clog 2 (b + 1) + 1) := width_upper b Δ
      _ ≤ 2 * Δ * (2 * Nat.clog 2 (b + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

variable {V : Type} [DecidableEq V]

def nextColor (b Δ : ℕ) (N : V → Finset V) (c : V → DeterministicColorReductionStep.Bits b) (v : V) :
    DeterministicColorReductionStep.Bits (width b Δ) :=
  encodeOutput b Δ (DeterministicColorReductionStep.output N c v)

/-- The received one-broadcast rule followed by actual local binary recoding. -/
def program (b Δ : ℕ) : Program V (DeterministicColorReductionStep.Bits b)
    (DeterministicColorReductionStep.Bits (width b Δ)) :=
  .seq (DeterministicColorReductionStep.program b) (.local fun _ _ S => encodeOutput b Δ S)

theorem rounds (b Δ : ℕ) : (program (V := V) b Δ).rounds = 1 := by
  simp only [program, Program.rounds, DeterministicColorReductionStep.rounds, Nat.add_zero]

theorem maxBits (b Δ : ℕ) : (program (V := V) b Δ).maxBits = b := by
  simp only [program, Program.maxBits, DeterministicColorReductionStep.maxBits, Nat.max_zero]

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (b Δ : ℕ) (c : V → DeterministicColorReductionStep.Bits b) (v : V) :
    (program b Δ).runEncoded G c v = nextColor b Δ (fun u => G.neighborFinset u) c v := by
  change encodeOutput b Δ ((DeterministicColorReductionStep.program b).runEncoded G c v) =
    encodeOutput b Δ (DeterministicColorReductionStep.output (fun u => G.neighborFinset u) c v)
  exact congrArg (encodeOutput b Δ) (DeterministicColorReductionStep.correct G b c v)

theorem output_size (b Δ : ℕ) (c : V → DeterministicColorReductionStep.Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (DeterministicColorReductionStep.output (fun u => G.neighborFinset u) c v).card ≤ Δ := by
  have hh := DeterministicColorReductionStep.local_size (fun u => G.neighborFinset u) c v
  exact hh.trans (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v)

theorem decode_next (b Δ : ℕ) (c : V → DeterministicColorReductionStep.Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (code b Δ).decode ((program b Δ).runEncoded G c v) =
      some ⟨DeterministicColorReductionStep.output (fun u => G.neighborFinset u) c v,
        output_size G b Δ c hdeg v⟩ := by
  rw [correct]
  unfold nextColor
  rw [encodeOutput_valid b Δ _ (output_size G b Δ c hdeg v)]
  exact decode_encode b Δ _

theorem proper (b Δ : ℕ) (c : V → DeterministicColorReductionStep.Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hc : ∀ u v, G.Adj u v → c u ≠ c v)
    (u v : V) (ha : G.Adj u v) :
    (program b Δ).runEncoded G c u ≠ (program b Δ).runEncoded G c v := by
  intro he
  have hd := congrArg (code b Δ).decode he
  rw [decode_next G b Δ c hdeg u, decode_next G b Δ c hdeg v] at hd
  exact DeterministicColorReductionStep.proper G b c hc u v ha
    (congrArg Subtype.val (Option.some.inj hd))

end Graph
end Paper.DeterministicColorReductionCodec

#print axioms Paper.DeterministicColorReductionCodec.code
#print axioms Paper.DeterministicColorReductionCodec.decode_encode
#print axioms Paper.DeterministicColorReductionCodec.decode_next
#print axioms Paper.DeterministicColorReductionCodec.proper
#print axioms Paper.DeterministicColorReductionCodec.width_logarithmic
#print axioms Paper.DeterministicColorReductionCodec.encode_zero_bits
#print axioms Paper.DeterministicColorReductionCodec.encode_zero_degree
#print axioms Paper.DeterministicColorReductionCodec.rounds
#print axioms Paper.DeterministicColorReductionCodec.maxBits
