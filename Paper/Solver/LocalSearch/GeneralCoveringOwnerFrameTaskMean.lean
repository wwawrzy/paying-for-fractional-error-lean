import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskData
import Paper.Preliminaries.LocalSeedExtension

/-! Exact projection of a decoded task's local finite mean onto public-V
Boolean coins. The observer is proof-side only; executable task inputs and
sparse solver answers are produced by the separate native programs.
Unused padded slots have no effect on the entire decoded task, including
its boundary function, and no slot type is assumed to embed into V. -/
namespace Paper.GeneralCoveringOwnerFrameTaskMean
open BroadcastModel GeneralCoveringOwnerFrameTaskData
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Arrays (Δ k b n : ℕ) := Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n

def restrict (Δ k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) : Arrays Δ k b n := fun j =>
  if h : j.val < (GeneralCoveringOwnerFramePartition.addresses xs).length then
    β ((GeneralCoveringOwnerFramePartition.addresses xs).get ⟨j.val, h⟩)
  else GeneralCoveringOwnerFramePartition.zeroBits Δ k b n

def arrayFromRecords (Δ k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (ys : List (V × ActiveFiniteBitPartition.Bits Δ k b n)) : Arrays Δ k b n :=
  restrict Δ k b n xs (FrameInterpreter.inputs ys (GeneralCoveringOwnerFramePartition.zeroBits Δ k b n))

def decoded {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (a : V) (mask : Fin (partSlots Δ k) → Bool) (ω : Arrays Δ k b n) : GeneralCoveringOwnerFrameTaskData.Task V :=
  compute I Δ k t b n a (encode Δ k b n mask ω) xs

theorem restrict_slot (Δ k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n)
    (j : Fin (GeneralCoveringOwnerFramePartition.addresses xs).length) :
    restrict Δ k b n xs β (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h j) =
      β ((GeneralCoveringOwnerFramePartition.addresses xs).get j) := by
  simp only [restrict, LocalSeedRecords.slot, dif_pos j.isLt]

/-- Independence of padding holds for all queried boundary values at once. -/
theorem used_slots {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n)
    (ω ν : Arrays Δ k b n)
    (he : ∀ j, ω (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h j) =
      ν (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h j)) :
    decoded I Δ k t b n xs a mask ω = decoded I Δ k t b n xs a mask ν := by
  have hs : seeds Δ k b n (encode Δ k b n mask ω) xs = seeds Δ k b n (encode Δ k b n mask ν) xs := by
    rw [seeds_records Δ k b n _ xs h, seeds_records Δ k b n _ xs h]
    apply congrArg (LocalSeedRecords.base (GeneralCoveringOwnerFramePartition.addresses xs))
    funext j
    simp only [coins_encode]
    exact congrArg (fun z => (true, z)) (he j)
  have hv : view I Δ k t b n (encode Δ k b n mask ω) xs = view I Δ k t b n (encode Δ k b n mask ν) xs := by
    funext u
    exact congrArg (fun ys => FrameInterpreter.evaluate (ActiveFiniteBitPartition.program I Δ k t b n) xs ys
      (true, GeneralCoveringOwnerFramePartition.zeroBits Δ k b n) u) hs
  simp only [decoded, compute, mask_encode, hv]

theorem records_decoded {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n) (ω : Arrays Δ k b n) :
    decoded I Δ k t b n xs a mask
      (arrayFromRecords Δ k b n xs (LocalSeedRecords.records (GeneralCoveringOwnerFramePartition.addresses xs) h ω)) =
        decoded I Δ k t b n xs a mask ω := by
  apply used_slots I Δ k t b n xs a mask h
  intro j
  rw [arrayFromRecords, restrict_slot]
  exact LocalSeedExtension.inputs_get (GeneralCoveringOwnerFramePartition.addresses xs) (Finset.sort_nodup _ _)
    (fun i => ω (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h i)) _ j

theorem base_decoded {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n)
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
    decoded I Δ k t b n xs a mask (arrayFromRecords Δ k b n xs
      (LocalSeedRecords.base (GeneralCoveringOwnerFramePartition.addresses xs)
        (fun j => β ((GeneralCoveringOwnerFramePartition.addresses xs).get j)))) =
      decoded I Δ k t b n xs a mask (restrict Δ k b n xs β) := by
  apply used_slots I Δ k t b n xs a mask h
  intro j
  rw [arrayFromRecords, restrict_slot, restrict_slot]
  exact LocalSeedRecords.inputs_base (GeneralCoveringOwnerFramePartition.addresses xs) β
    (GeneralCoveringOwnerFramePartition.zeroBits Δ k b n) _ ((GeneralCoveringOwnerFramePartition.addresses xs).get_mem j)

variable [Fintype V]

/-- Exact local/global mean equality for any downstream natural task observer. -/
theorem mean {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n) (f : GeneralCoveringOwnerFrameTaskData.Task V → ℕ) :
    (∑ ω : Arrays Δ k b n, (f (decoded I Δ k t b n xs a mask ω) : ℝ)) / Fintype.card (Arrays Δ k b n) =
      (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (f (decoded I Δ k t b n xs a mask (restrict Δ k b n xs β)) : ℝ)) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
  let l := GeneralCoveringOwnerFramePartition.addresses xs
  let event := fun ys => f (decoded I Δ k t b n xs a mask (arrayFromRecords Δ k b n xs ys))
  have hm := FiniteLocalMean.numerator_mean_eq l (Finset.sort_nodup _ _) h event
  have hn : (FiniteLocalMean.numerator l h event : ℝ) =
      ∑ ω : Arrays Δ k b n, (f (decoded I Δ k t b n xs a mask ω) : ℝ) := by
    rw [FiniteLocalMean.numerator, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ω _
    exact congrArg (fun z => (f z : ℝ)) (records_decoded I Δ k t b n xs a mask h ω)
  rw [hn] at hm
  have hden : FiniteLocalMean.denominator (ActiveFiniteBitPartition.Bits Δ k b n) (frameSlots Δ k n) =
      Fintype.card (Arrays Δ k b n) := by simp only [Arrays, Fintype.card_fun, Fintype.card_fin, FiniteLocalMean.denominator]
  rw [hden] at hm
  apply hm.trans
  apply congrArg (fun z : ℝ => z / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  exact congrArg (fun z => (f z : ℝ)) (base_decoded I Δ k t b n xs a mask h β)

end Paper.GeneralCoveringOwnerFrameTaskMean

#print axioms Paper.GeneralCoveringOwnerFrameTaskMean.restrict_slot
#print axioms Paper.GeneralCoveringOwnerFrameTaskMean.used_slots
#print axioms Paper.GeneralCoveringOwnerFrameTaskMean.records_decoded
#print axioms Paper.GeneralCoveringOwnerFrameTaskMean.base_decoded
#print axioms Paper.GeneralCoveringOwnerFrameTaskMean.mean
