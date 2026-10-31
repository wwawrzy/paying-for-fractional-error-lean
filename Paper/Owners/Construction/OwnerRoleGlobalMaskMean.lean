import Paper.Owners.Construction.OwnerRoleConfigurationMean
import Paper.Averaging.Tasks.TaskRoleSum
import Paper.Owners.Construction.OwnerRoleScoreAbsent

/-! The actual bounded own numerator equals the exact global-source mean
of mask-role scores. Global V/source enumeration occurs only in this proof. -/
namespace Paper.OwnerRoleGlobalMaskMean
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem all_anchors {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hk : k ≤ r)
    (c : V → Fin (B + 1)) (v : V) :
    (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) =
      ∑ anchor : V, ∑ i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s),
        (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) : ℝ) := by
  have hh := congrArg (fun n : ℕ => (n : ℝ))
    (OwnerRoleNumerator.exact_sum G C D R hcover L Δ r k t Q T s a B q M hQ hk c v)
  simp only [Nat.cast_sum] at hh
  rw [TaskRoleSum.space] at hh
  change _ = ∑ anchor ∈ RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D R L Δ r v),
    ∑ i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s),
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) : ℝ) at hh
  apply hh.trans
  apply Finset.sum_subset (Finset.subset_univ _)
  intro anchor _ hnot
  apply Finset.sum_eq_zero
  intro i _
  simpa only [Nat.cast_zero] using congrArg (fun n : ℕ => (n : ℝ))
    (OwnerRoleScoreAbsent.anchor G C D R L Δ r k t Q T s a B q M hQ c v anchor hnot i)

theorem configuration_mean {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V) :
    (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
        (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ) =
      (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        ∑ anchor : V, ∑ mask : Fin ((Δ + 1) ^ k) → Bool,
          (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
            (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ)) /
              (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) : ℝ) := by
  rw [all_anchors G C D R hcover L Δ r k t Q T s a B q M hQ (by omega) c v, Finset.sum_div]
  simp_rw [OwnerRoleConfigurationMean.all_metadata G C D R hcover L Δ r k t Q T s a B q M hQ hks c v]
  rw [← Finset.sum_div, Finset.sum_comm]

end Paper.OwnerRoleGlobalMaskMean
