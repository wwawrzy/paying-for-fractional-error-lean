import Paper.Averaging.Tasks.TaskAllReduce
import Paper.Averaging.Tasks.TaskMinimum
import Paper.Preliminaries.BinaryCounter

/-! Exact counts of a fixed number of selected subsets, and a minimum-ID
query. Every active physical task vertex receives the answer. -/
namespace Paper.TaskQueries
open BroadcastModel CappedCount
variable {V : Type} [LinearOrder V]

def countProgram {b : ℕ} (C : BitCode V b) (m D : ℕ) :=
  TaskAllReduce.program C (PacketCode.vector (BinaryCounter.countCode b) m) D

def minimumProgram {b : ℕ} (C : BitCode V b) (D : ℕ) :=
  TaskAllReduce.program C (MinimumPayload.code C) D

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem counts {b : ℕ} (C : BitCode V b) (m : ℕ)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (S : Fin m → Finset V)
    (hS : ∀ i, S i ⊆ PhysicalTasks.vertices G D R L Q I) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      (((countProgram C m (4 * k)).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I),
          fun i => cap (2 ^ b) (if u ∈ S i then 1 else 0))) v).2.map
            (fun f i => (f i).value.val)) = some (fun i => (S i).card) := by
  let weights : V → Fin m → Count (2 ^ b) := fun u i =>
    cap (2 ^ b) (if u ∈ S i then 1 else 0)
  have hz : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → weights u = 0 := by
    intro u hu
    funext i
    have hs : u ∉ S i := fun hs => hu (hS i hs)
    simp [weights, hs, cap_zero]
  have hsum : (∑ u, weights u) = fun i => cap (2 ^ b) (S i).card := by
    funext i
    simp only [Finset.sum_apply, weights]
    rw [← cap_sum]
    simp
  have he : (fun i => (cap (2 ^ b) (S i).card).value.val) = fun i => (S i).card := by
    funext i
    exact min_eq_left ((Finset.card_le_univ (S i)).trans (BinaryCounter.order_bound C))
  intro v hv
  have hres := TaskAllReduce.physical_task G C
    (PacketCode.vector (BinaryCounter.countCode b) m) D R L Q I hI k hsize weights hz v hv
  change ((TaskAllReduce.program C (PacketCode.vector (BinaryCounter.countCode b) m) (4 * k)).run G
    (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), weights u)) v).2.map _ = _
  rw [hres, Option.map_some, hsum]
  exact congrArg some he

theorem minimum {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (S : Finset V)
    (hS : S ⊆ PhysicalTasks.vertices G D R L Q I) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      (((minimumProgram C (4 * k)).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I),
          if u ∈ S then MinimumPayload.singleton u else 0)) v).2.map
            MinimumPayload.Data.value) = some (MaskedMinimum.minimum S) := by
  have hz : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I →
      (if u ∈ S then MinimumPayload.singleton u else (0 : MinimumPayload.Data V)) = 0 := by
    intro u hu
    have hs : u ∉ S := fun hs => hu (hS hs)
    simp [hs]
  intro v hv
  have hres := TaskAllReduce.physical_task G C (MinimumPayload.code C)
    D R L Q I hI k hsize (fun u => if u ∈ S then MinimumPayload.singleton u else 0) hz v hv
  change ((TaskAllReduce.program C (MinimumPayload.code C) (4 * k)).run G _ v).2.map _ = _
  rw [hres, Option.map_some, TaskMinimum.sum_selected]
  rfl

theorem count_rounds {b : ℕ} (C : BitCode V b) (m k : ℕ) :
    (countProgram C m (4 * k)).rounds = 16 * k + 1 := by
  rw [countProgram, TaskAllReduce.rounds]
  omega

theorem count_logarithmic_bits {b : ℕ} (C : BitCode V b) (m k n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (countProgram C m (4 * k)).maxBits ≤
      ((2 * m + 1) * (c + 1) + 4 * k + 2) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + m * (2 * (b + 1)) + 1 ≤
      ((2 * m + 1) * (c + 1)) * Nat.clog 2 (n + 2) := by
    have hs := Nat.mul_le_mul_left (2 * m + 1) hids
    have hc := Nat.mul_le_mul_left (2 * m + 1) hl
    nlinarith
  have hd : 4 * k + 2 ≤ (4 * k + 2) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * k + 2) hl
  apply (TaskAllReduce.maxBits C (PacketCode.vector (BinaryCounter.countCode b) m) (4 * k)).trans
  apply max_le <;> nlinarith

theorem minimum_rounds {b : ℕ} (C : BitCode V b) (k : ℕ) :
    (minimumProgram C (4 * k)).rounds = 16 * k + 1 := by
  rw [minimumProgram, TaskAllReduce.rounds]
  omega

theorem minimum_logarithmic_bits {b : ℕ} (C : BitCode V b) (k n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (minimumProgram C (4 * k)).maxBits ≤
      (2 * (c + 1) + 4 * k + 2) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : 2 * b + 2 ≤ (2 * (c + 1)) * Nat.clog 2 (n + 2) := by
    nlinarith
  have hd : 4 * k + 2 ≤ (4 * k + 2) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * k + 2) hl
  apply (TaskAllReduce.maxBits C (MinimumPayload.code C) (4 * k)).trans
  apply max_le <;> nlinarith
end Paper.TaskQueries
