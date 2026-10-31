import Paper.Averaging.Tasks.TaskQueries
import Paper.Preliminaries.NeighborhoodCount
import Paper.Solver.LocalSearch.LocalSearchBounds

/-! Actual computation of heavy-candidate flags: exact task demand count
followed by one demand-bit broadcast and a local integer comparison. -/
namespace Paper.HeavyEligibility
open BroadcastModel
variable {V : Type} [LinearOrder V]

def countInput (b : ℕ) (s : Bool × Bool) : Bool × (Fin 1 → CappedCount.Count (2 ^ b)) :=
  (s.1, fun _ => CappedCount.cap (2 ^ b) (if s.2 then 1 else 0))

def countPrepare (b : ℕ) : Program V (Bool × Bool)
    ((Bool × (Fin 1 → CappedCount.Count (2 ^ b))) × (Bool × Bool)) :=
  .local fun _ _ s => (countInput b s, s)

def countFinish {b : ℕ} : Program V
    (PayloadFlood.State (Fin 1 → CappedCount.Count (2 ^ b)) × (Bool × Bool))
    (Option ℕ × (Bool × Bool)) :=
  .local fun _ _ s => (s.1.2.map (fun f => (f 0).value.val), s.2)

def countStage {b : ℕ} (C : BitCode V b) (D : ℕ) :
    Program V (Bool × Bool) (Option ℕ × (Bool × Bool)) :=
  .seq (countPrepare b) (.seq (ProgramMemory.carry (TaskQueries.countProgram C 1 D)) countFinish)

def neighborPrepare : Program V (Option ℕ × (Bool × Bool)) (Bool × (Bool × Option ℕ)) :=
  .local fun _ _ s => (s.2.2, (s.2.1, s.1))

def finish (m : ℕ) : Program V (ℕ × (Bool × Option ℕ)) (Bool × Bool) :=
  .local fun _ _ s => (s.2.1, match s.2.2 with
    | none => false
    | some a => decide (a ≤ m * s.1))

def program {b : ℕ} (C : BitCode V b) (D m : ℕ) : Program V (Bool × Bool) (Bool × Bool) :=
  .seq (countStage C D) (.seq neighborPrepare
    (.seq (ProgramMemory.carry NeighborhoodCount.program) (finish m)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_countStage {b : ℕ} (C : BitCode V b) (D : ℕ) (s : V → Bool × Bool) :
    (countStage C D).run G s = fun v =>
      ((((TaskQueries.countProgram C 1 D).run G (fun u => countInput b (s u)) v).2.map
        (fun f => (f 0).value.val)), s v) := by
  change countFinish.run G ((ProgramMemory.carry (TaskQueries.countProgram C 1 D)).run G
    (fun v => (countInput b (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_program {b : ℕ} (C : BitCode V b) (D m : ℕ) (s : V → Bool × Bool) :
    (program C D m).run G s = fun v => ((s v).1,
      match (((TaskQueries.countProgram C 1 D).run G (fun u => countInput b (s u)) v).2.map
        (fun f => (f 0).value.val)) with
      | none => false
      | some a => decide (a ≤ m * (NeighborhoodCount.program.run G (fun u => (s u).2) v))) := by
  change (finish m).run G ((ProgramMemory.carry NeighborhoodCount.program).run G
    (neighborPrepare.run G ((countStage C D).run G s))) = _
  rw [run_countStage]
  change (finish m).run G ((ProgramMemory.carry NeighborhoodCount.program).run G
    (fun v => ((s v).2, ((s v).1,
      ((TaskQueries.countProgram C 1 D).run G (fun u => countInput b (s u)) v).2.map
        (fun f => (f 0).value.val))))) = _
  rw [ProgramMemory.run]
  rfl

theorem active {b : ℕ} (C : BitCode V b) (D m : ℕ) (s : V → Bool × Bool) (v : V) :
    ((program C D m).run G s v).1 = (s v).1 := by rw [run_program]

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (A : Finset V)
    (hA : A ⊆ PhysicalTasks.vertices G D R L Q I) (m : ℕ) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((program C (4 * k) m).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) v).2 =
          decide (A.card ≤ m * (SevenFoundation.closed G v ∩ A).card) := by
  have hi : (fun u => countInput b
      (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) =
      fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I),
        fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0)) := by
    funext u
    simp [countInput]
  intro v hv
  have hcounts := TaskQueries.counts G C 1 D R L Q I hI k hsize (fun _ => A) (fun _ => hA) v hv
  have hscalar := congrArg (Option.map (fun f : Fin 1 → ℕ => f 0)) hcounts
  simp only [Option.map_map, Option.map_some] at hscalar
  change (((TaskQueries.countProgram C 1 (4 * k)).run G
    (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I),
      fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0))) v).2.map
        (fun f => (f 0).value.val)) = some A.card at hscalar
  rw [run_program, hi]
  change (match _ with
    | none => false
    | some a => decide (a ≤ m * (NeighborhoodCount.program.run G (fun u => decide (u ∈ A)) v))) = _
  rw [hscalar, NeighborhoodCount.eval_eq]

theorem rounds {b : ℕ} (C : BitCode V b) (D m : ℕ) :
    (program C D m).rounds = 4 * D + 2 := by
  simp [program, countStage, countPrepare, countFinish, neighborPrepare, finish,
    Program.rounds, ProgramMemory.rounds, TaskQueries.countProgram, TaskAllReduce.rounds,
    NeighborhoodCount.program]

theorem maxBits {b : ℕ} (C : BitCode V b) (D m : ℕ) :
    (program C D m).maxBits ≤ max (3 * b + 3) (D + 2) := by
  have hc : (countStage C D).maxBits = (TaskQueries.countProgram C 1 D).maxBits := by
    simp [countStage, countPrepare, countFinish, Program.maxBits, ProgramMemory.maxBits]
  have hq : (TaskQueries.countProgram C 1 D).maxBits ≤ max (3 * b + 3) (D + 2) := by
    have hh := TaskAllReduce.maxBits C (PacketCode.vector (BinaryCounter.countCode b) 1) D
    have hw : b + 1 * (2 * (b + 1)) + 1 = 3 * b + 3 := by omega
    rw [hw] at hh
    exact hh
  change max (countStage C D).maxBits
    (max neighborPrepare.maxBits (max (ProgramMemory.carry NeighborhoodCount.program).maxBits
      (finish m).maxBits)) ≤ _
  simp only [neighborPrepare, finish, Program.maxBits, ProgramMemory.maxBits,
    NeighborhoodCount.program, Nat.max_zero, Nat.zero_max]
  rw [hc]
  exact max_le hq (by omega)
end Paper.HeavyEligibility
