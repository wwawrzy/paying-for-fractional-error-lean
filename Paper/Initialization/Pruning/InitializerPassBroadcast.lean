import Paper.Initialization.Lists.InitializerListBroadcast

/-! A complete physical initialization pass: two flags, actual recursive
bounded-list selection, empty-list self selections, and residual update.
Runtime input is only the vertex's own current residual bit. -/
namespace Paper.InitializerPassBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

def duplicate : Program V Bool (Bool × Bool) := .local fun _ _ s => (s, s)

def prepareCore : Program V ((Finset V × Bool) × Bool) (Finset V × (Bool × Bool)) :=
  .local fun _ _ s => (s.1.1, (s.1.2, s.2))

def finishCore : Program V (Bool × (Bool × Bool)) (Bool × Bool) :=
  .local fun _ _ s => (s.1 || s.2.1, s.2.2)

def selection {b : ℕ} (C : BitCode V b) (a h f : ℕ) : Program V Bool (Bool × Bool) :=
  .seq duplicate (.seq (ProgramMemory.carry (InitializerListBroadcast.program h f))
    (.seq prepareCore (.seq (ProgramMemory.carry (CoreSelectionBroadcast.program C f (2 * a))) finishCore)))

def prepareResidual : Program V (Bool × Bool) (Bool × (Bool × Bool)) :=
  .local fun _ _ s => (s.1, s)

def finishResidual : Program V (Finset V × (Bool × Bool)) (Bool × Bool) :=
  .local fun _ _ s => (s.2.1, s.2.2 && decide (s.1 = ∅))

def program {b : ℕ} (C : BitCode V b) (a h f : ℕ) : Program V Bool (Bool × Bool) :=
  .seq (selection C a h f) (.seq prepareResidual
    (.seq (ProgramMemory.carry FlagNeighborhood.program) finishResidual))

variable [Fintype V]

theorem selection_rounds {b : ℕ} (C : BitCode V b) (a h f : ℕ) :
    (selection C a h f).rounds = 3 + 2 * f := by
  simp only [selection, duplicate, prepareCore, finishCore, Program.rounds,
    ProgramMemory.rounds, InitializerListBroadcast.rounds, CoreSelectionBroadcast.rounds,
    Nat.zero_add, Nat.add_zero]
  omega

theorem rounds {b : ℕ} (C : BitCode V b) (a h f : ℕ) : (program C a h f).rounds = 4 + 2 * f := by
  simp only [program, prepareResidual, finishResidual, Program.rounds, selection_rounds,
    ProgramMemory.rounds, FlagNeighborhood.rounds, Nat.zero_add, Nat.add_zero]
  omega

theorem selection_maxBits {b : ℕ} (C : BitCode V b) (a h f : ℕ) :
    (selection C a h f).maxBits ≤ max 1 (f * (b + 1)) := by
  simp only [selection, duplicate, prepareCore, finishCore, Program.maxBits,
    ProgramMemory.maxBits, InitializerListBroadcast.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le (le_max_left _ _) (CoreSelectionBroadcast.maxBits C f (2 * a))

theorem maxBits {b : ℕ} (C : BitCode V b) (a h f : ℕ) :
    (program C a h f).maxBits ≤ max 1 (f * (b + 1)) := by
  simp only [program, prepareResidual, finishResidual, Program.maxBits,
    ProgramMemory.maxBits, FlagNeighborhood.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le (selection_maxBits C a h f) (le_max_left _ _)
end Paper.InitializerPassBroadcast
