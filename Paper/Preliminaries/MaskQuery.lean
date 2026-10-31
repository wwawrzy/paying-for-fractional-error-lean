import Paper.Preliminaries.CostTag
import Paper.Preliminaries.LocalDemandMask

/-! Actual minimum-cost representative query for one incidence mask.
Each vertex computes its mask and cost/ID tag from private local input. -/
namespace Paper.MaskQuery
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  demands : List V

def queryInput {B : ℕ} (T : ℕ) (z : Fin T → Bool) (v : V) (N : Finset V) (s : Input V B) :
    Bool × MinimumPayload.Data (CostTag.Tag V B) :=
  (s.active, if s.active = true ∧ LocalDemandMask.mask T s.demands v N = z then
    MinimumPayload.singleton (toLex (s.cost, v)) else 0)

def prepare (B T : ℕ) (z : Fin T → Bool) : Program V (Input V B)
    ((Bool × MinimumPayload.Data (CostTag.Tag V B)) × Input V B) :=
  .local fun v N s => (queryInput T z v N s, s)

def finish (B : ℕ) : Program V
    (PayloadFlood.State (MinimumPayload.Data (CostTag.Tag V B)) × Input V B)
    (Input V B × Option (CostTag.Tag V B)) :=
  .local fun _ _ s => (s.2, (s.1.2.map MinimumPayload.Data.value).getD none)

def program {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) :=
  Program.seq (prepare B T z) (.seq
    (ProgramMemory.carry (TaggedMinimum.program C (CostTag.code C B) D)) (finish B))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def fiber (H : Finset V) (T : ℕ) (l : List V) (z : Fin T → Bool) : Finset V :=
  H.filter (fun v => LocalDemandMask.mask T l v (G.neighborFinset v) = z)

theorem run_program {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) (s : V → Input V B) :
    (program C D B T z).run G s = fun v => (s v,
      ((((TaggedMinimum.program C (CostTag.code C B) D).run G
        (fun u => queryInput T z u (G.neighborFinset u) (s u)) v).2.map
          MinimumPayload.Data.value).getD none)) := by
  change (finish B).run G ((ProgramMemory.carry
    (TaggedMinimum.program C (CostTag.code C B) D)).run G
      (fun v => (queryInput T z v (G.neighborFinset v) (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem input_eq (H : Finset V) (B T : ℕ) (l : List V) (z : Fin T → Bool)
    (cost : V → Fin (B + 1)) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ H)) (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ H, (s v).demands = l) :
    (fun v => queryInput T z v (G.neighborFinset v) (s v)) = fun v =>
      (decide (v ∈ H), if v ∈ fiber G H T l z then
        MinimumPayload.singleton (CostTag.tag cost v) else 0) := by
  funext v
  dsimp only [queryInput]
  rw [ha v, hc v]
  by_cases hv : v ∈ H
  · rw [hl v hv]
    simp [fiber, hv, CostTag.tag]
  · simp [fiber, hv]

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (B T : ℕ) (l : List V) (z : Fin T → Bool)
    (cost : V → Fin (B + 1)) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, (s v).demands = l) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((program C (4 * k) B T z).run G s v).2 =
        MaskedMinimum.minimum ((fiber G (PhysicalTasks.vertices G D R L Q I) T l z).image
          (CostTag.tag cost)) := by
  intro v hv
  have hi := input_eq G _ B T l z cost s ha hc hl
  have hres := TaggedMinimum.physical_task G C (CostTag.code C B) D R L Q I hI k hsize
    (fiber G (PhysicalTasks.vertices G D R L Q I) T l z) (Finset.filter_subset _ _)
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
end Paper.MaskQuery
