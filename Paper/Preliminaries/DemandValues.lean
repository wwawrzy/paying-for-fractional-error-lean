import Paper.Averaging.Tasks.TaskAllReduce
import Paper.Preliminaries.CappedCount
import Paper.Preliminaries.ListPacket

/-! Actual query for residual multiplicities at a bounded list of demand
IDs. A list entry has just one contributing physical vertex, so a constant
q-counter suffices even when the task has arbitrarily many vertices. -/
namespace Paper.DemandValues
open BroadcastModel CappedCount
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (q : ℕ) where
  active : Bool
  value : Fin (q + 1)
  demands : List V

def queryInput {q : ℕ} (T : ℕ) (v : V) (s : Input V q) : Bool × (Fin T → Count q) :=
  (s.active, fun i => if s.active then
    cap q (if s.demands[i.val]? = some v then s.value.val else 0) else 0)

def prepare (q T : ℕ) : Program V (Input V q) ((Bool × (Fin T → Count q)) × Input V q) :=
  .local fun v _ s => (queryInput T v s, s)

def finish (q T : ℕ) : Program V
    (PayloadFlood.State (Fin T → Count q) × Input V q) (Input V q × Option (Fin T → ℕ)) :=
  .local fun _ _ s => (s.2, s.1.2.map (fun f i => (f i).value.val))

def program {b : ℕ} (C : BitCode V b) (D q T : ℕ) :=
  Program.seq (prepare q T) (.seq
    (ProgramMemory.carry (TaskAllReduce.program C (PacketCode.vector (code q) T) D)) (finish q T))

variable [Fintype V]

def weights (H : Finset V) (q T : ℕ) (l : List V) (multiplicity : V → Fin (q + 1))
    (v : V) : Fin T → Count q := fun i => if v ∈ H then
      cap q (if l[i.val]? = some v then (multiplicity v).val else 0) else 0

def values (T : ℕ) (l : List V) {q : ℕ} (multiplicity : V → Fin (q + 1)) : Fin T → ℕ := fun i =>
  match l[i.val]? with
  | none => 0
  | some r => (multiplicity r).val

theorem input_eq (H : Finset V) (q T : ℕ) (l : List V) (multiplicity : V → Fin (q + 1))
    (s : V → Input V q) (ha : ∀ v, (s v).active = decide (v ∈ H))
    (hb : ∀ v, (s v).value = multiplicity v) (hl : ∀ v ∈ H, (s v).demands = l) :
    (fun v => queryInput T v (s v)) = fun v => (decide (v ∈ H), weights H q T l multiplicity v) := by
  funext v
  dsimp only [queryInput]
  rw [ha v, hb v]
  by_cases hv : v ∈ H
  · rw [hl v hv]
    apply Prod.ext
    · rfl
    · funext i
      simp [weights, hv]
  · apply Prod.ext
    · rfl
    · funext i
      simp [weights, hv]

theorem sum_weights (H : Finset V) (q T : ℕ) (l : List V) (multiplicity : V → Fin (q + 1))
    (hl : ∀ r ∈ l, r ∈ H) :
    (∑ v, weights H q T l multiplicity v) = fun i => cap q (values T l multiplicity i) := by
  funext i
  rw [Finset.sum_apply]
  cases hi : l[i.val]? with
  | none => simp [weights, values, hi, cap_zero]
  | some r =>
    have hr : r ∈ H := hl r (List.mem_iff_getElem?.mpr ⟨i.val, hi⟩)
    rw [Finset.sum_eq_single r]
    · simp [weights, values, hi, hr]
    · intro v _ hv
      simp [weights, hi, Ne.symm hv, cap_zero]
    · simp

theorem decoded_values (q T : ℕ) (l : List V) (multiplicity : V → Fin (q + 1)) :
    (fun i => (cap q (values T l multiplicity i)).value.val) = values T l multiplicity := by
  funext i
  cases hi : l[i.val]? with
  | none => simp [values, hi, cap]
  | some r =>
    change min (values T l multiplicity i) q = values T l multiplicity i
    simp only [values, hi]
    exact min_eq_left (by have := (multiplicity r).isLt; omega)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D q T : ℕ) (s : V → Input V q) :
    (program C D q T).run G s = fun v => (s v,
      ((TaskAllReduce.program C (PacketCode.vector (code q) T) D).run G
        (fun u => queryInput T u (s u)) v).2.map (fun f i => (f i).value.val)) := by
  change (finish q T).run G ((ProgramMemory.carry
    (TaskAllReduce.program C (PacketCode.vector (code q) T) D)).run G
      (fun v => (queryInput T v (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (q T : ℕ) (l : List V)
    (multiplicity : V → Fin (q + 1)) (s : V → Input V q)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hb : ∀ v, (s v).value = multiplicity v)
    (hl : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, (s v).demands = l)
    (hlist : ∀ r ∈ l, r ∈ PhysicalTasks.vertices G D R L Q I) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((program C (4 * k) q T).run G s v).2 = some (values T l multiplicity) := by
  let H := PhysicalTasks.vertices G D R L Q I
  have hz : ∀ v, v ∉ H → weights H q T l multiplicity v = 0 := by
    intro v hv
    funext i
    simp [weights, hv]
  intro v hv
  have hi := input_eq H q T l multiplicity s ha hb hl
  have hres := TaskAllReduce.physical_task G C (PacketCode.vector (code q) T)
    D R L Q I hI k hsize (weights H q T l multiplicity) hz v hv
  rw [run_program, hi]
  dsimp only
  rw [hres, Option.map_some, sum_weights H q T l multiplicity hlist]
  exact congrArg some (decoded_values q T l multiplicity)

theorem rounds {b : ℕ} (C : BitCode V b) (D q T : ℕ) :
    (program C D q T).rounds = 4 * D + 1 := by
  simp [program, prepare, finish, Program.rounds, ProgramMemory.rounds, TaskAllReduce.rounds]

theorem maxBits {b : ℕ} (C : BitCode V b) (D q T : ℕ) :
    (program C D q T).maxBits ≤ max (b + T * (q + 1) + 1) (D + 2) := by
  simpa only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits,
    Nat.max_zero, Nat.zero_max] using TaskAllReduce.maxBits C (PacketCode.vector (code q) T) D
end Paper.DemandValues
