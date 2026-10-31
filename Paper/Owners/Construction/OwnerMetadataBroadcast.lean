import Paper.Owners.Construction.OwnerRootBroadcast
import Paper.Owners.Construction.OwnerInteraction

/-! Actual four-round physical owner/repair metadata. All support sets
are private received data; each message is one bit or one ID plus a bit. -/
namespace Paper.OwnerMetadataBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  center : Bool
  demand : Bool
  owner : V
  augmented : Finset V
  heavy : Bool
  remaining : Bool
  support : Finset V

def root : Program V (Bool × Bool) (State V) :=
  .seq (.local fun _ _ s => (s.1, s)) (.seq (ProgramMemory.carry OwnerRootBroadcast.program)
    (.local fun _ _ s => ⟨s.2.1, s.2.2, s.1, ∅, false, false, ∅⟩))

def augmented {b : ℕ} (C : BitCode V b) (L : ℕ) : Program V (State V) (State V) :=
  .seq (.local fun _ _ s => ((s.owner, s.center || s.demand), s))
    (.seq (ProgramMemory.carry (LabelNeighborhood.program C))
      (.local fun _ _ s => { s.2 with augmented := s.1, heavy := decide (L < s.1.card) }))

def repair : Program V (State V) (State V) :=
  .seq (.local fun _ _ s => (s.heavy, s)) (.seq (ProgramMemory.carry FlagNeighborhood.program)
    (.local fun _ _ s => { s.2 with remaining := s.2.demand && decide (s.1 = ∅) }))

def actual {b : ℕ} (C : BitCode V b) : Program V (State V) (State V) :=
  .seq (.local fun _ _ s => ((s.owner, s.remaining), s))
    (.seq (ProgramMemory.carry (LabelNeighborhood.program C))
      (.local fun _ _ s => { s.2 with support := s.1 }))

def program {b : ℕ} (C : BitCode V b) (L : ℕ) : Program V (Bool × Bool) (State V) :=
  .seq root (.seq (augmented C L) (.seq repair (actual C)))

variable [Fintype V]

theorem root_rounds : (root (V := V)).rounds = 1 := rfl

theorem augmented_rounds {b : ℕ} (C : BitCode V b) (L : ℕ) : (augmented C L).rounds = 1 := rfl

theorem repair_rounds : (repair (V := V)).rounds = 1 := rfl

theorem actual_rounds {b : ℕ} (C : BitCode V b) : (actual C).rounds = 1 := rfl

theorem rounds {b : ℕ} (C : BitCode V b) (L : ℕ) : (program C L).rounds = 4 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (L : ℕ) : (program C L).maxBits = b + 1 := by
  simp only [program, root, augmented, repair, actual, Program.maxBits, ProgramMemory.maxBits,
    OwnerRootBroadcast.maxBits, LabelNeighborhood.maxBits, FlagNeighborhood.maxBits, Nat.zero_max, Nat.max_zero]
  omega

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L).maxBits ≤ (c + 1) * Nat.clog 2 (n + 2) := by
  rw [maxBits]
  exact (BroadcastModel.logarithmic_message_budget n b c hids).1
end Paper.OwnerMetadataBroadcast
