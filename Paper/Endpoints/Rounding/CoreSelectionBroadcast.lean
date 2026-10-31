import Paper.Preliminaries.CohostKnown
import Paper.Preliminaries.IncidentPhase
import Paper.Communication.ProgramMemory

/-! Literal bounded-list/core selection program. One initial list exchange
and two bit/report broadcasts per rank level. All core enumeration and
minimum-ID decisions are private finite computation. -/
namespace Paper.CoreSelectionBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  ownList : Finset V
  incident : Finset (Finset V)
  selected : Bool

def prepareKnown : Program V (State V) ((Finset V × Bool) × State V) :=
  .local fun _ _ s => ((s.ownList, s.selected), s)

def finishKnown (q n : ℕ) : Program V (Finset V × State V) (State V) :=
  .local fun v _ s => ⟨s.2.ownList, s.2.incident,
    IncidentPhase.chosen v (IncidentHierarchy.localLevel v s.2.incident q n) s.1 s.2.selected⟩

def step {b : ℕ} (C : BitCode V b) (f q n : ℕ) : Program V (State V) (State V) :=
  .seq prepareKnown (.seq (ProgramMemory.carry (CohostKnown.program C f)) (finishKnown q n))

def body {b : ℕ} (C : BitCode V b) (f q n : ℕ) : ℕ → Program V (State V) (State V)
  | 0 => .local fun _ _ s => ⟨s.ownList, s.incident, false⟩
  | j + 1 => .seq (body C f q (n + 1) j) (step C f q n)

def start : Program V (Finset V) (Finset V × Finset V) := .local fun _ _ s => (s, s)

def initializeState : Program V (Finset (Finset V) × Finset V) (State V) :=
  .local fun _ _ s => ⟨s.2, s.1, false⟩

def program {b : ℕ} (C : BitCode V b) (f q : ℕ) : Program V (Finset V) Bool :=
  .seq start (.seq (ProgramMemory.carry (ListIncidenceBroadcast.program C f))
    (.seq initializeState (.seq (body C f q 0 f) (.local fun _ _ s => s.selected))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {b : ℕ} (C : BitCode V b) (f q n : ℕ) (s : V → State V) :
    (step C f q n).run G s = fun v => ⟨(s v).ownList, (s v).incident,
      IncidentPhase.chosen v (IncidentHierarchy.localLevel v (s v).incident q n)
        ((CohostKnown.program C f).run G (fun u => ((s u).ownList, (s u).selected)) v) (s v).selected⟩ := by
  change (finishKnown q n).run G ((ProgramMemory.carry (CohostKnown.program C f)).run G
    (fun u => (((s u).ownList, (s u).selected), s u))) = _
  rw [ProgramMemory.run]
  rfl

theorem body_metadata {b : ℕ} (C : BitCode V b) (f q n j : ℕ) (s : V → State V) :
    ∀ v, ((body C f q n j).run G s v).ownList = (s v).ownList ∧
      ((body C f q n j).run G s v).incident = (s v).incident := by
  induction j generalizing n s with
  | zero => exact fun _ => ⟨rfl, rfl⟩
  | succ j ih =>
    intro v
    change ((step C f q n).run G ((body C f q (n + 1) j).run G s) v).ownList = _ ∧ _
    rw [run_step]
    exact ih (n + 1) s v

theorem body_rounds {b : ℕ} (C : BitCode V b) (f q n j : ℕ) : (body C f q n j).rounds = 2 * j := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [body, step, prepareKnown, finishKnown, Program.rounds, ProgramMemory.rounds,
      CohostKnown.rounds, Nat.zero_add, Nat.add_zero, ih]
    omega

theorem body_maxBits {b : ℕ} (C : BitCode V b) (f q n j : ℕ) :
    (body C f q n j).maxBits ≤ max 1 (f * (b + 1)) := by
  induction j generalizing n with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    apply max_le (ih (n + 1))
    simp only [step, prepareKnown, finishKnown, Program.maxBits, ProgramMemory.maxBits,
      CohostKnown.maxBits, Nat.zero_max, Nat.max_zero]
    exact le_rfl

theorem rounds {b : ℕ} (C : BitCode V b) (f q : ℕ) : (program C f q).rounds = 1 + 2 * f := by
  simp only [program, start, initializeState, Program.rounds, ProgramMemory.rounds,
    ListIncidenceBroadcast.rounds, body_rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (f q : ℕ) :
    (program C f q).maxBits ≤ max 1 (f * (b + 1)) := by
  simp only [program, start, initializeState, Program.maxBits, ProgramMemory.maxBits,
    ListIncidenceBroadcast.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le (le_max_right _ _) (body_maxBits C f q 0 f)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (f q n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C f q).maxBits ≤ (1 + f * (c + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hw := ListPacket.logarithmic_width f b c n hids
  apply (maxBits C f q).trans
  apply max_le <;> nlinarith
end Paper.CoreSelectionBroadcast
