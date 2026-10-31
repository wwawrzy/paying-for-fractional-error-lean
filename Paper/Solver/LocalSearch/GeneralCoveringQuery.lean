import Paper.Solver.LocalSearch.GeneralCoveringMask
import Paper.Averaging.Tasks.ActiveTaskMasks

/-! A concrete broadcast minimum-cost query for arbitrary incidence masks.
Only cost/ID tags are communicated. Directed covering lists remain private. -/
namespace Paper.GeneralCoveringQuery
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  demands : List V
  targets : Finset V

def queryInput {B : ℕ} (T : ℕ) (z : Fin T → Bool) (v : V) (s : Input V B) :
    Bool × MinimumPayload.Data (CostTag.Tag V B) :=
  (s.active, if s.active = true ∧ GeneralCoveringMask.mask T s.demands s.targets = z then
    MinimumPayload.singleton (toLex (s.cost, v)) else 0)

def prepare (B T : ℕ) (z : Fin T → Bool) : Program V (Input V B)
    ((Bool × MinimumPayload.Data (CostTag.Tag V B)) × Input V B) :=
  .local fun v _ s => (queryInput T z v s, s)

def finish (B : ℕ) : Program V
    (PayloadFlood.State (MinimumPayload.Data (CostTag.Tag V B)) × Input V B)
    (Input V B × Option (CostTag.Tag V B)) :=
  .local fun _ _ s => (s.2, (s.1.2.map MinimumPayload.Data.value).getD none)

def program {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) :=
  Program.seq (prepare B T z) (.seq
    (ProgramMemory.carry (TaggedMinimum.program C (CostTag.code C B) D)) (finish B))

def fiber (H : Finset V) (T : ℕ) (l : List V) (targets : V → Finset V)
    (z : Fin T → Bool) : Finset V :=
  H.filter (fun v => GeneralCoveringMask.mask T l (targets v) = z)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool)
    (s : V → Input V B) :
    (program C D B T z).run G s = fun v => (s v,
      ((((TaggedMinimum.program C (CostTag.code C B) D).run G
        (fun u => queryInput T z u (s u)) v).2.map
          MinimumPayload.Data.value).getD none)) := by
  change (finish B).run G ((ProgramMemory.carry
    (TaggedMinimum.program C (CostTag.code C B) D)).run G
      (fun v => (queryInput T z v (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

omit [Fintype V] in
theorem input_eq (H : Finset V) (B T : ℕ) (l : List V) (targets : V → Finset V)
    (z : Fin T → Bool) (cost : V → Fin (B + 1)) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ H)) (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ H, (s v).demands = l) (ht : ∀ v ∈ H, (s v).targets = targets v) :
    (fun v => queryInput T z v (s v)) = fun v =>
      (decide (v ∈ H), if v ∈ fiber H T l targets z then
        MinimumPayload.singleton (CostTag.tag cost v) else 0) := by
  funext v
  dsimp only [queryInput]
  rw [ha v, hc v]
  by_cases hv : v ∈ H
  · rw [hl v hv, ht v hv]
    simp [fiber, hv, CostTag.tag]
  · simp [fiber, hv]

/-- Every active vertex receives the cheapest cost/ID tag in the requested
incidence class, using the existing physical communication network. -/
theorem active_task (K : ActiveTask.Context G) {b : ℕ} (C : BitCode V b)
    (B T : ℕ) (l : List V) (targets : V → Finset V) (z : Fin T → Bool)
    (cost : V → Fin (B + 1)) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l)
    (ht : ∀ v ∈ K.vertices, (s v).targets = targets v) :
    ∀ v ∈ K.vertices, ((program C K.diameter B T z).run G s v).2 =
      MaskedMinimum.minimum ((fiber K.vertices T l targets z).image (CostTag.tag cost)) := by
  intro v hv
  have hi := input_eq K.vertices B T l targets z cost s ha hc hl ht
  have hres := ActiveTaskMasks.taggedMinimum G K C (CostTag.code C B)
    (fiber K.vertices T l targets z) (Finset.filter_subset _ _)
    (CostTag.tag cost) (CostTag.injective cost) v hv
  rw [run_program, hi]
  dsimp only
  rw [hres]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) :
    (program C D B T z).rounds = 4 * D + 1 := by
  simp [program, prepare, finish, Program.rounds, ProgramMemory.rounds,
    TaggedMinimum.program, TaskAllReduce.rounds]

theorem maxBits {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) :
    (program C D B T z).maxBits ≤ max (2 * b + B + 3) (D + 2) := by
  have hh := TaskAllReduce.maxBits C (MinimumPayload.code (CostTag.code C B)) D
  have hw : b + (B + 1 + b + 1) + 1 = 2 * b + B + 3 := by omega
  rw [hw] at hh
  simpa only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits,
    Nat.max_zero, Nat.zero_max, TaggedMinimum.program] using hh

end Paper.GeneralCoveringQuery

#print axioms Paper.GeneralCoveringQuery.active_task
#print axioms Paper.GeneralCoveringQuery.rounds
#print axioms Paper.GeneralCoveringQuery.maxBits
