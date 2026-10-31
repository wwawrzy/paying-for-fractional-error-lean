import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairUnion
import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameFractional

/-! Actual deterministic fractional runtime with one original frame producer.
The task solver's retained environment feeds the two-round repair observer;
its root packets feed one joint boundary-event count. Own output is a
bounded natural numerator over a fixed public product denominator. -/
namespace Paper.GeneralCoveringOwnerFrameAverage
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwnerFrameTaskInputs.Input V B
abbrev TaskOutput (V : Type) (L Δ a B k b n q : ℕ) :=
  GeneralCoveringOwnerFrameFractional.Output V L Δ a B k b n q

def repairDenominator (L Δ k b n : ℕ) : ℕ := GeneralCoveringOwnerRepairUnion.denominator L Δ k b n
  (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)

def denominator (L Δ k b n q : ℕ) : ℕ :=
  GeneralCoveringOwnerFrameFractional.denominator Δ k b n q * repairDenominator L Δ k b n

def numeratorBound (L Δ a B k b n q : ℕ) : ℕ :=
  GeneralCoveringOwnerFrameFractional.numeratorBound L Δ a B k b n q * repairDenominator L Δ k b n +
    GeneralCoveringOwnerFrameFractional.denominator Δ k b n q * repairDenominator L Δ k b n

def rootFrames {L Δ a B k b n q : ℕ} (s : TaskOutput V L Δ a B k b n q) :
    GeneralCoveringOwnerRootFrames.Output V L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n) :=
  s.2.2.1.source

def combine {L Δ a B k b n q : ℕ}
    (p : Fin (GeneralCoveringOwnerFrameFractional.numeratorBound L Δ a B k b n q + 1))
    (h : ℕ) (hh : h ≤ repairDenominator L Δ k b n) : Fin (numeratorBound L Δ a B k b n q + 1) :=
  ⟨p.val * repairDenominator L Δ k b n + GeneralCoveringOwnerFrameFractional.denominator Δ k b n q * h,
    Nat.lt_succ_of_le (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ p.isLt))
      (Nat.mul_le_mul_left _ hh))⟩

abbrev Saved (V : Type) (L Δ a B k b n q : ℕ) :=
  GeneralCoveringOwnerRepairObserver.Output V × TaskOutput V L Δ a B k b n q
abbrev Output (V : Type) (L Δ a B k b n q : ℕ) :=
  Fin (numeratorBound L Δ a B k b n q + 1) × Saved V L Δ a B k b n q

def prepare (L Δ a B k b n q : ℕ) : Program V (TaskOutput V L Δ a B k b n q)
    (GeneralCoveringOwnerVirtualPrepare.Env V × TaskOutput V L Δ a B k b n q) :=
  .local fun _ _ s => ((rootFrames s).env, s)

def finish {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) :
    Program V (Saved V L Δ a B k b n q) (Output V L Δ a B k b n q) :=
  .local fun _ _ s =>
    let h := GeneralCoveringOwnerRepairUnion.count I k t b n (rootFrames s.2) s.1
    (combine s.2.1 h (GeneralCoveringOwnerRepairUnion.count_le I k t b n (rootFrames s.2) s.1), s)

/-- No global input map or global coin assignment is a runtime argument. -/
def program {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V L Δ a B k b n q) :=
  .seq (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB)
    (.seq (prepare L Δ a B k b n q)
      (.seq (ProgramMemory.carry (GeneralCoveringOwnerRepairObserver.core I)) (finish I L Δ a B k t b n q)))

theorem denominator_pos (L Δ k b n q : ℕ) (hq : 0 < q) : 0 < denominator L Δ k b n q :=
  Nat.mul_pos (GeneralCoveringOwnerFrameFractional.denominator_pos Δ k b n q hq)
    (FiniteLocalMean.denominator_pos _)

theorem rounds {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program I L Δ a B k t b n q hB).rounds =
      (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).rounds + 2 := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringOwnerRepairObserver.rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits [Fintype V] {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program I L Δ a B k t b n q hB).maxBits =
      max (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).maxBits (ids + 3) := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringOwnerRepairObserver.maxBits, Nat.zero_max, Nat.max_zero]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rootFrames_retained {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    rootFrames ((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v) =
      (GeneralCoveringOwnerRootFrames.program I L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)).runEncoded G
        (fun u => (s u).1) v := by
  change ((GeneralCoveringOwnerFrameFractional.sparse I L Δ a B k t b n q hB).runEncoded G s v).2.1.source = _
  rw [GeneralCoveringOwnerFrameFractional.run_sparse]
  change ((GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).runEncoded G s v).2.1.source = _
  rw [GeneralCoveringOwnerFrameTaskInputs.source_retained]
  exact GeneralCoveringOwnerRoleFrames.source_retained G I L Δ
    (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n) k (GeneralCoveringOwnerFrameTaskData.frameRadius k n)
    (fun u => (s u).1) v

theorem run_program {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program I L Δ a B k t b n q hB).runEncoded G s =
      let p := (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s
      let o := (GeneralCoveringOwnerRepairObserver.core I).runEncoded G (fun u => (rootFrames (p u)).env)
      fun v =>
        (combine (p v).1 (GeneralCoveringOwnerRepairUnion.count I k t b n (rootFrames (p v)) (o v))
          (GeneralCoveringOwnerRepairUnion.count_le I k t b n (rootFrames (p v)) (o v)), (o v, p v)) := by
  simp only [Program.runEncoded_eq_run]
  change (finish I L Δ a B k t b n q).run G
    ((ProgramMemory.carry (GeneralCoveringOwnerRepairObserver.core I)).run G
      (fun u => ((rootFrames ((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).run G s u)).env,
        (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).run G s u))) = _
  rw [ProgramMemory.run]
  rfl

theorem task_retained {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program I L Δ a B k t b n q hB).runEncoded G s v).2.2 =
      (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v := by
  rw [run_program]

theorem observer_retained {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program I L Δ a B k t b n q hB).runEncoded G s v).2.1 =
      (GeneralCoveringOwnerRepairObserver.core I).runEncoded G
        (GeneralCoveringOwnerRepairFrames.environments G L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)
          (fun u => (s u).1) I) v := by
  rw [run_program]
  have he : (fun u => (rootFrames ((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s u)).env) =
      GeneralCoveringOwnerRepairFrames.environments G L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)
        (fun u => (s u).1) I := by
    funext u
    exact congrArg GeneralCoveringOwnerRootFrames.Output.env
      (rootFrames_retained G I L Δ a B k t b n q hB s u)
  change (GeneralCoveringOwnerRepairObserver.core I).runEncoded G _ v = _
  rw [he]

theorem numerator {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    (((program I L Δ a B k t b n q hB).runEncoded G s v).1).val =
      (((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val *
        repairDenominator L Δ k b n +
      GeneralCoveringOwnerFrameFractional.denominator Δ k b n q *
        GeneralCoveringOwnerRepairUnion.count I k t b n
          (rootFrames ((program I L Δ a B k t b n q hB).runEncoded G s v).2.2)
          ((program I L Δ a B k t b n q hB).runEncoded G s v).2.1 := by
  rw [run_program]
  rfl

end Paper.GeneralCoveringOwnerFrameAverage

#print axioms Paper.GeneralCoveringOwnerFrameAverage.denominator_pos
#print axioms Paper.GeneralCoveringOwnerFrameAverage.rounds
#print axioms Paper.GeneralCoveringOwnerFrameAverage.maxBits
#print axioms Paper.GeneralCoveringOwnerFrameAverage.rootFrames_retained
#print axioms Paper.GeneralCoveringOwnerFrameAverage.run_program
#print axioms Paper.GeneralCoveringOwnerFrameAverage.task_retained
#print axioms Paper.GeneralCoveringOwnerFrameAverage.observer_retained
#print axioms Paper.GeneralCoveringOwnerFrameAverage.numerator
