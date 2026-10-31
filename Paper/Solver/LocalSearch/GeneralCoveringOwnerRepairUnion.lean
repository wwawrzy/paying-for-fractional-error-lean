import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairFrames
import Paper.Solver.LocalSearch.GeneralCoveringOwnerFramePartition
import Paper.Averaging.Tasks.FiniteLocalMean

/-! One joint finite coin space for the union of the received root frames.
Every boundary query uses the same seed records, so shared repair requests
retain their exact correlations. The public padding bound depends only on
packet capacities, never on a physical dependency ball or the size of V. -/
namespace Paper.GeneralCoveringOwnerRepairUnion
open BroadcastModel NeighborBalls
open GeneralCoveringOwnerFramePartition
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def slots (L Δ r : ℕ) : ℕ := max 1 L * GeneralCoveringOwnerRootFrames.capacity Δ r

def window {L Δ r : ℕ} (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) :
    List (TopologyGather.Record V Δ) := RootFrameUnion.records z.roots.val

private theorem records_length {Δ r : ℕ}
    (xs : List (V × GeneralCoveringOwnerRootFrames.Frame V Δ r)) :
    (RootFrameUnion.records xs).length ≤ xs.length * GeneralCoveringOwnerRootFrames.capacity Δ r := by
  induction xs with
  | nil =>
    have he : RootFrameUnion.records ([] : List (V × GeneralCoveringOwnerRootFrames.Frame V Δ r)) = [] :=
      List.flatMap_nil (f := fun p : V × GeneralCoveringOwnerRootFrames.Frame V Δ r => p.2.val)
    rw [he]
    exact Nat.zero_le _
  | cons p xs ih =>
    have he : RootFrameUnion.records (p :: xs) = p.2.val ++ RootFrameUnion.records xs :=
      List.flatMap_cons (f := fun q : V × GeneralCoveringOwnerRootFrames.Frame V Δ r => q.2.val)
    calc
      _ = (p.2.val ++ RootFrameUnion.records xs).length := congrArg List.length he
      _ = p.2.val.length + (RootFrameUnion.records xs).length := List.length_append
      _ ≤ GeneralCoveringOwnerRootFrames.capacity Δ r +
          xs.length * GeneralCoveringOwnerRootFrames.capacity Δ r := Nat.add_le_add p.2.property ih
      _ = _ := by rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

theorem capacity {L Δ r : ℕ} (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) :
    (addresses (window z)).length ≤ slots L Δ r := by
  rw [addresses, Finset.length_sort]
  have hk : (TaggedDictionary.keys (window z)).card ≤ (window z).length := by
    simpa only [TaggedDictionary.keys, List.length_map] using List.toFinset_card_le ((window z).map Prod.fst)
  exact hk.trans ((records_length z.roots.val).trans (Nat.mul_le_mul_right _ z.roots.property))

def seeds (Δ k b n : ℕ) (ys : List (V × Bits Δ k b n)) :
    List (V × ActiveFiniteBitPartition.Input Δ k b n) := ys.map (fun p => (p.1, (true, p.2)))

def boundary {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (ys : List (V × Bits Δ k b n)) (u : V) : Bool :=
  (FrameInterpreter.evaluate (ActiveFiniteBitPartition.program I Δ k t b n) xs (seeds Δ k b n ys)
    (true, zeroBits Δ k b n) u).2

def event {ids L Δ r : ℕ} (I : BitCode V ids) (k t b n : ℕ)
    (z : GeneralCoveringOwnerRootFrames.Output V L Δ r)
    (o : GeneralCoveringOwnerRepairObserver.Output V) (ys : List (V × Bits Δ k b n)) : ℕ :=
  if GeneralCoveringOwnerRepairObserver.evaluate o.fixed o.roots
    (boundary I Δ k t b n (window z) ys) then 1 else 0

def count {ids L Δ r : ℕ} (I : BitCode V ids) (k t b n : ℕ)
    (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) (o : GeneralCoveringOwnerRepairObserver.Output V) : ℕ :=
  FiniteLocalMean.numerator (addresses (window z)) (capacity z) (event I k t b n z o)

def denominator (L Δ k b n r : ℕ) : ℕ := FiniteLocalMean.denominator (Bits Δ k b n) (slots L Δ r)

theorem count_le {ids L Δ r : ℕ} (I : BitCode V ids) (k t b n : ℕ)
    (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) (o : GeneralCoveringOwnerRepairObserver.Output V) :
    count I k t b n z o ≤ denominator L Δ k b n r := by
  have h := FiniteLocalMean.numerator_le _ (capacity z) (event I k t b n z o) 1 (by
    intro ω
    unfold event
    split <;> omega)
  simpa only [count, denominator, Nat.mul_one] using h

variable [Fintype V]

/-- This is the full joint event mean, including every overlap between roots.
The equality holds even when the public padded slot count exceeds |V|. -/
theorem mean {ids L Δ r : ℕ} (I : BitCode V ids) (k t b n : ℕ)
    (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) (o : GeneralCoveringOwnerRepairObserver.Output V) :
    (count I k t b n z o : ℝ) / denominator L Δ k b n r =
      (∑ β : V → Bits Δ k b n, (event I k t b n z o
        (LocalSeedRecords.base (addresses (window z)) (fun i => β ((addresses (window z)).get i))) : ℝ)) /
          Fintype.card (V → Bits Δ k b n) :=
  FiniteLocalMean.numerator_mean_eq _ (Finset.sort_nodup _ _) (capacity z) _

end Paper.GeneralCoveringOwnerRepairUnion

#print axioms Paper.GeneralCoveringOwnerRepairUnion.capacity
#print axioms Paper.GeneralCoveringOwnerRepairUnion.count_le
#print axioms Paper.GeneralCoveringOwnerRepairUnion.mean
