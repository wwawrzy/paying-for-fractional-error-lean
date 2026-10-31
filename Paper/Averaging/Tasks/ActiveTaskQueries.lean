import Paper.Averaging.Tasks.TaskQueries

/-! Actual task queries for arbitrary nonempty finite active sets with
proved diameter. No owner-specific task equality is required by the API. -/
namespace Paper.ActiveTaskQueries
open BroadcastModel CappedCount
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem allReduce {A : Type} [AddCommMonoid A] {b c : ℕ}
    (C : BitCode V b) (F : BitCode A c) (H : Finset V) (hne : H.Nonempty) (D : ℕ)
    (hd : ∀ x y : ↥(H : Set V), ∃ p : (G.induce (H : Set V)).Walk x y, p.length ≤ D)
    (weights : V → A) (hz : ∀ v, v ∉ H → weights v = 0) :
    ∀ v ∈ H, ((TaskAllReduce.program C F D).run G
      (fun u => (decide (u ∈ H), weights u)) v).2 = some (∑ u, weights u) := by
  have hs := (TaskTree.induced G C H hne D hd).1
  intro v hv
  exact TaskAllReduce.correct G C F D _ (H.min' hne) hs
    (decide_eq_true (Finset.min'_mem H hne)) weights
    (fun u hu => hz u (by simpa only [decide_eq_false_iff_not] using hu)) v (decide_eq_true hv)

theorem counts {b : ℕ} (C : BitCode V b) (H : Finset V) (hne : H.Nonempty) (D m : ℕ)
    (hd : ∀ x y : ↥(H : Set V), ∃ p : (G.induce (H : Set V)).Walk x y, p.length ≤ D)
    (S : Fin m → Finset V) (hS : ∀ i, S i ⊆ H) : ∀ v ∈ H,
      (((TaskQueries.countProgram C m D).run G
        (fun u => (decide (u ∈ H), fun i => cap (2 ^ b) (if u ∈ S i then 1 else 0))) v).2.map
          (fun f i => (f i).value.val)) = some (fun i => (S i).card) := by
  let weights : V → Fin m → Count (2 ^ b) := fun u i => cap (2 ^ b) (if u ∈ S i then 1 else 0)
  have hz : ∀ u, u ∉ H → weights u = 0 := by
    intro u hu
    funext i
    have hs : u ∉ S i := fun h => hu (hS i h)
    simp only [weights, if_neg hs, cap_zero, Pi.zero_apply]
  have hsum : (∑ u, weights u) = fun i => cap (2 ^ b) (S i).card := by
    funext i
    simp only [Finset.sum_apply, weights]
    rw [← cap_sum]
    simp
  have he : (fun i => (cap (2 ^ b) (S i).card).value.val) = fun i => (S i).card := by
    funext i
    exact min_eq_left ((Finset.card_le_univ (S i)).trans (BinaryCounter.order_bound C))
  intro v hv
  have hres := allReduce G C (PacketCode.vector (BinaryCounter.countCode b) m) H hne D hd weights hz v hv
  change ((TaskAllReduce.program C (PacketCode.vector (BinaryCounter.countCode b) m) D).run G
    (fun u => (decide (u ∈ H), weights u)) v).2.map _ = _
  rw [hres, Option.map_some, hsum]
  exact congrArg some he

theorem minimum {b : ℕ} (C : BitCode V b) (H : Finset V) (hne : H.Nonempty) (D : ℕ)
    (hd : ∀ x y : ↥(H : Set V), ∃ p : (G.induce (H : Set V)).Walk x y, p.length ≤ D)
    (S : Finset V) (hS : S ⊆ H) : ∀ v ∈ H,
      (((TaskQueries.minimumProgram C D).run G
        (fun u => (decide (u ∈ H), if u ∈ S then MinimumPayload.singleton u else 0)) v).2.map
          MinimumPayload.Data.value) = some (MaskedMinimum.minimum S) := by
  have hz : ∀ u, u ∉ H → (if u ∈ S then MinimumPayload.singleton u else (0 : MinimumPayload.Data V)) = 0 := by
    intro u hu
    have hs : u ∉ S := fun h => hu (hS h)
    simp only [if_neg hs]
  intro v hv
  have hres := allReduce G C (MinimumPayload.code C) H hne D hd
    (fun u => if u ∈ S then MinimumPayload.singleton u else 0) hz v hv
  change ((TaskAllReduce.program C (MinimumPayload.code C) D).run G _ v).2.map _ = _
  rw [hres, Option.map_some, TaskMinimum.sum_selected]
  rfl
end Paper.ActiveTaskQueries
