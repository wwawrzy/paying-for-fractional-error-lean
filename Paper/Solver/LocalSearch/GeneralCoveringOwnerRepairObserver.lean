import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepair

/-! Actual two-round acquisition of all potential boundary repair sources.
Partners come from the original private metadata and one center-bit round.
The next broadcast sends one optional partner ID and two own flag bits.
The receiver retains the fixed high/heavy contribution and the union of
low-owner sources whose boundary flags can select this physical vertex. -/
namespace Paper.GeneralCoveringOwnerRepairObserver
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  partner : Option V

structure Output (V : Type) where
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  partner : Option V
  fixed : Bool
  roots : Finset V

def high (s : State V) : Bool := s.env.high && s.env.metadata.owned.input.center
def low (s : State V) : Bool := s.env.low && s.env.metadata.owned.input.center

abbrev Message (V : Type) := (Option V × Bool) × Bool

def message (s : State V) : Message V := ((s.partner, high s), low s)
def highMessage (s : Message V) : Option V := if s.1.2 then s.1.1 else none

def roots (v : V) (N : Finset V) (s : State V) (incoming : N → Message V) : Finset V :=
  (if low s then {v} else ∅) ∪
    (N.attach.filter (fun u => (incoming u).2 = true ∧ (incoming u).1.1 = some v)).image Subtype.val

def assemble (v : V) (N : Finset V) (s : State V) (incoming : N → Message V) : Output V :=
  ⟨s.env, s.partner,
    s.env.metadata.heavy || high s ||
      decide (v ∈ MaskedMinimum.pool N (highMessage (message s)) (fun u => highMessage (incoming u))),
    roots v N s incoming⟩

def round : Round V (State V) (Output V) (Message V) where
  send _ _ s := message s
  update := assemble

def requestProgram {b : ℕ} (ids : BitCode V b) : Program V (State V) (Output V) :=
  .broadcast (b + 1 + 1 + 1) ids.option.pairBool.pairBool round

def prepare : Program V (GeneralCoveringOwnerVirtualPrepare.Env V)
    (GeneralCoveringOwnerSupport.State V × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .local fun _ _ s => (s.metadata, s)

def prepareState : Program V
    (GeneralCoveringPartners.Output V × GeneralCoveringOwnerVirtualPrepare.Env V) (State V) :=
  .local fun _ _ s => ⟨s.2, s.1.partner⟩

/-- The supplied environment is the retained actual producer output. -/
def core {b : ℕ} (ids : BitCode V b) :
    Program V (GeneralCoveringOwnerVirtualPrepare.Env V) (Output V) :=
  .seq prepare (.seq (ProgramMemory.carry GeneralCoveringPartners.attach)
    (.seq prepareState (requestProgram ids)))

def evaluate (fixed : Bool) (T : Finset V) (boundary : V → Bool) : Bool :=
  fixed || (T.sort (· ≤ ·)).any boundary

theorem evaluate_iff (fixed : Bool) (T : Finset V) (boundary : V → Bool) :
    evaluate fixed T boundary = true ↔ fixed = true ∨ ∃ u ∈ T, boundary u = true := by
  simp only [evaluate, Bool.or_eq_true, List.any_eq_true, Finset.mem_sort]

theorem mem_pool (N : Finset V) (self : Option V) (incoming : N → Option V) (v : V) :
    v ∈ MaskedMinimum.pool N self incoming ↔ self = some v ∨ ∃ u : N, incoming u = some v := by
  constructor
  · exact MaskedMinimum.pool_origin N self incoming
      (fun v => self = some v ∨ ∃ u : N, incoming u = some v)
      (fun _ h => Or.inl h) (fun u _ h => Or.inr ⟨u, h⟩)
  · rintro (h | ⟨u, h⟩)
    · exact MaskedMinimum.mem_pool_self N incoming h
    · exact MaskedMinimum.mem_pool_incoming N self incoming u h

theorem conditional_some (flag : Bool) (p : Option V) (v : V) :
    (if flag then p else none) = some v ↔ flag = true ∧ p = some v := by
  cases flag <;> simp

theorem roots_iff (v : V) (N : Finset V) (s : State V) (incoming : N → Message V) (u : V) :
    u ∈ roots v N s incoming ↔ (low s = true ∧ u = v) ∨
      ∃ w : N, w.val = u ∧ (incoming w).2 = true ∧ (incoming w).1.1 = some v := by
  cases h : low s <;> simp [roots, h, Finset.mem_image, Finset.mem_filter, and_comm, and_left_comm]

theorem roots_event (v : V) (N : Finset V) (s : State V) (incoming : N → Message V) (boundary : V → Bool) :
    (∃ u ∈ roots v N s incoming, boundary u = true) ↔
      (low s = true ∧ boundary v = true) ∨
        ∃ w : N, (incoming w).2 = true ∧ (incoming w).1.1 = some v ∧ boundary w.val = true := by
  constructor
  · rintro ⟨u, hu, hb⟩
    rcases (roots_iff v N s incoming u).mp hu with ⟨hl, rfl⟩ | ⟨w, rfl, hl, hp⟩
    · exact Or.inl ⟨hl, hb⟩
    · exact Or.inr ⟨w, hl, hp, hb⟩
  · rintro (⟨hl, hb⟩ | ⟨w, hl, hp, hb⟩)
    · exact ⟨v, (roots_iff v N s incoming v).mpr (Or.inl ⟨hl, rfl⟩), hb⟩
    · exact ⟨w.val, (roots_iff v N s incoming w.val).mpr (Or.inr ⟨w, rfl, hl, hp⟩), hb⟩

def markedState (boundary : V → Bool) (s : V → State V) (v : V) : GeneralCoveringOwnerRepair.State V :=
  ⟨(s v).env, high (s v) || (low (s v) && boundary v), (s v).partner⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def states (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (v : V) : State V :=
  ⟨E v, (GeneralCoveringPartners.attach.run G (fun u => (E u).metadata) v).partner⟩

theorem run_core {b : ℕ} (ids : BitCode V b) (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) :
    (core ids).runEncoded G E = (requestProgram ids).runEncoded G (states G E) := by
  simp only [Program.runEncoded_eq_run]
  change (requestProgram ids).run G (prepareState.run G
    ((ProgramMemory.carry GeneralCoveringPartners.attach).run G (fun v => ((E v).metadata, E v)))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_request {b : ℕ} (ids : BitCode V b) (s : V → State V) (v : V) :
    (requestProgram ids).run G s v =
      assemble v (G.neighborFinset v) (s v) (fun u => message (s u.val)) := rfl

/-- Exact union logic for the literal request broadcast. The same optional
partner IDs are used in both actual executions. -/
theorem request_selected {b : ℕ} (ids : BitCode V b) (s : V → State V) (boundary : V → Bool) (v : V) :
    ((GeneralCoveringOwnerRepair.requestProgram ids).run G (markedState boundary s) v).selected =
      evaluate ((requestProgram ids).run G s v).fixed ((requestProgram ids).run G s v).roots boundary := by
  apply Bool.eq_iff_iff.mpr
  change (GeneralCoveringOwnerRepair.assemble (markedState boundary s v)
    (decide (v ∈ MaskedMinimum.pool (G.neighborFinset v)
      (GeneralCoveringOwnerRepair.message (markedState boundary s v))
      (fun u => GeneralCoveringOwnerRepair.message (markedState boundary s u.val))))).selected = true ↔ _
  rw [run_request, evaluate_iff]
  simp only [GeneralCoveringOwnerRepair.assemble, markedState, assemble,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, mem_pool,
    GeneralCoveringOwnerRepair.message, conditional_some, highMessage, message, roots_event]
  aesop

/-- Actual Partners.attach execution, with the same immutable Env as the
accepted repair core. This is not a supplied request-list contract. -/
theorem core_selected {b : ℕ} (ids : BitCode V b) (E : V → GeneralCoveringOwnerVirtualPrepare.Env V)
    (boundary : V → Bool) (v : V) :
    ((GeneralCoveringOwnerRepair.core ids).runEncoded G
      (fun u => ⟨E u, (E u).high || ((E u).low && boundary u)⟩) v).selected =
      evaluate ((core ids).runEncoded G E v).fixed ((core ids).runEncoded G E v).roots boundary := by
  rw [run_core]
  simp only [Program.runEncoded_eq_run]
  rw [GeneralCoveringOwnerRepair.run_core]
  have hs : (fun u =>
      (⟨E u, ((E u).high || ((E u).low && boundary u)) && (E u).metadata.owned.input.center,
        (GeneralCoveringPartners.attach.run G (fun w => (E w).metadata) u).partner⟩ : GeneralCoveringOwnerRepair.State V)) =
        markedState boundary (states G E) := by
    funext u
    unfold markedState states high low
    congr 1
    cases (E u).high <;> cases (E u).low <;> cases boundary u <;>
      cases (E u).metadata.owned.input.center <;> rfl
  rw [hs]
  exact request_selected G ids (states G E) boundary v

theorem rounds {b : ℕ} (ids : BitCode V b) : (core ids).rounds = 2 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) : (core ids).maxBits = b + 3 := by
  simp only [core, prepare, prepareState, requestProgram, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringPartners.attach_maxBits, Nat.zero_max]
  omega

end Paper.GeneralCoveringOwnerRepairObserver

#print axioms Paper.GeneralCoveringOwnerRepairObserver.evaluate_iff
#print axioms Paper.GeneralCoveringOwnerRepairObserver.mem_pool
#print axioms Paper.GeneralCoveringOwnerRepairObserver.roots_iff
#print axioms Paper.GeneralCoveringOwnerRepairObserver.roots_event
#print axioms Paper.GeneralCoveringOwnerRepairObserver.run_core
#print axioms Paper.GeneralCoveringOwnerRepairObserver.request_selected
#print axioms Paper.GeneralCoveringOwnerRepairObserver.core_selected
#print axioms Paper.GeneralCoveringOwnerRepairObserver.rounds
#print axioms Paper.GeneralCoveringOwnerRepairObserver.maxBits
