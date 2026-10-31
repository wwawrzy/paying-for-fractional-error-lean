import Paper.Owners.Construction.OwnerPayloadRead
import Paper.Preliminaries.TaggedOwnedGather

/-! Literal four-round physical root-payload router. Every construction
depends only on local metadata, private own payload and fixed public codes.
Full owner-path delivery is proved separately from this composition. -/
namespace Paper.OwnerPayloadRoute
open BroadcastModel
variable {V A : Type} [LinearOrder V]

structure Input (V A : Type) where
  metadata : OwnerMetadataBroadcast.State V
  active : Bool
  payload : A

def readInput (s : Input V A) : OwnerPayloadRead.Input V A :=
  ⟨s.metadata.owner, s.metadata.remaining, s.active, s.payload⟩

def prepare : Program V (Input V A) (OwnerPayloadRead.Input V A × OwnerMetadataBroadcast.State V) :=
  .local fun _ _ s => (readInput s, s.metadata)

def toList : Program V (Option (V × A) × OwnerMetadataBroadcast.State V)
    (List (V × A) × OwnerMetadataBroadcast.State V) := .local fun _ _ s => (s.1.toList, s.2)

def ownedInput : Program V (List (V × A) × OwnerMetadataBroadcast.State V) (TaggedOwnedGather.Input V A) :=
  .local fun _ _ s => ⟨s.2.owner, s.2.remaining, s.1⟩

def program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    Program V (Input V A) (List (V × A)) :=
  .seq prepare (.seq (ProgramMemory.carry (OwnerPayloadRead.program P)) (.seq toList
    (.seq (ProgramMemory.carry (TaggedGather.program C P 1))
      (.seq (ProgramMemory.carry (TaggedGather.program C P L))
        (.seq ownedInput (TaggedOwnedGather.program C P (Δ + 1)))))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def first {w : ℕ} (P : BitCode A w) (s : V → Input V A) :=
  (OwnerPayloadRead.program P).run G (fun u => readInput (s u))

def candidate {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (s : V → Input V A) :=
  (TaggedGather.program C P 1).run G (fun u => (first G P s u).toList)

def demand {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ) (s : V → Input V A) :=
  (TaggedGather.program C P L).run G (candidate G C P s)

def finalInput {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ) (s : V → Input V A) (u : V) :
    TaggedOwnedGather.Input V A := ⟨(s u).metadata.owner, (s u).metadata.remaining, demand G C P L s u⟩

theorem run_program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A) :
    (program C P L Δ).run G s = (TaggedOwnedGather.program C P (Δ + 1)).run G (finalInput G C P L s) := by
  change (TaggedOwnedGather.program C P (Δ + 1)).run G (ownedInput.run G
    ((ProgramMemory.carry (TaggedGather.program C P L)).run G
      ((ProgramMemory.carry (TaggedGather.program C P 1)).run G (toList.run G
        ((ProgramMemory.carry (OwnerPayloadRead.program P)).run G (fun u => (readInput (s u), (s u).metadata))))))) = _
  rw [ProgramMemory.run G (OwnerPayloadRead.program P)]
  change (TaggedOwnedGather.program C P (Δ + 1)).run G (ownedInput.run G
    ((ProgramMemory.carry (TaggedGather.program C P L)).run G
      ((ProgramMemory.carry (TaggedGather.program C P 1)).run G (fun u => ((first G P s u).toList, (s u).metadata))))) = _
  rw [ProgramMemory.run G (TaggedGather.program C P 1)]
  change (TaggedOwnedGather.program C P (Δ + 1)).run G (ownedInput.run G
    ((ProgramMemory.carry (TaggedGather.program C P L)).run G (fun u => (candidate G C P s u, (s u).metadata)))) = _
  rw [ProgramMemory.run G (TaggedGather.program C P L)]
  rfl

theorem rounds {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (program C P L Δ).rounds = 4 := rfl

theorem maxBits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (program C P L Δ).maxBits ≤ (L + Δ + 3) * (b + w + 1) := by
  simp only [program, prepare, toList, ownedInput, Program.maxBits, ProgramMemory.maxBits,
    OwnerPayloadRead.maxBits, TaggedGather.maxBits, TaggedOwnedGather.maxBits, Nat.zero_max, Nat.max_zero, Nat.one_mul]
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · apply max_le <;> nlinarith

theorem logarithmic_bits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L Δ n c d : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : w ≤ d * Nat.clog 2 (n + 2)) :
    (program C P L Δ).maxBits ≤ ((L + Δ + 3) * (c + d + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + w + 1 ≤ (c + d + 1) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits C P L Δ).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb
end Paper.OwnerPayloadRoute
