import Paper.Owners.Construction.OwnerRoleFiniteSource

/-! Exact finite configuration mean of genuine physical role outputs.
The fixed public denominator accounts for all unused padding coordinates. -/
namespace Paper.OwnerRoleConfigurationMean
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem fixed_mask {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V) (mask : Fin ((Δ + 1) ^ k) → Bool) :
    (∑ ω : Fin ((Δ + 1) ^ s) → PriorityPartitionBroadcast.Table Δ k Q T,
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
        (TaskRoleId.make anchor (RoleTableEncoding.pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) mask ω)) : ℝ)) /
        (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ) =
      (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
          (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ)) /
            (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) : ℝ) := by
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let l := OwnerRoleFiniteSource.addresses G D R L Δ s anchor
  let hF := CanonicalRoleFrame.addresses_length G D R L Δ s anchor
  let f := OwnerRoleFiniteSource.fromRecords G C D R L Δ r k t Q T s a B q M hQ c v anchor mask
  have hl : l.Nodup := by
    unfold l OwnerRoleFiniteSource.addresses OwnerRoleTaskData.addresses
    exact Finset.sort_nodup _ _
  have hm := FiniteLocalMean.mean_eq l hl hF f
  have hleft : (∑ ω : Fin ((Δ + 1) ^ s) → PriorityPartitionBroadcast.Table Δ k Q T,
      f (LocalSeedRecords.records l hF ω)) =
      ∑ ω : Fin ((Δ + 1) ^ s) → PriorityPartitionBroadcast.Table Δ k Q T,
        (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
          (TaskRoleId.make anchor (RoleTableEncoding.pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) mask ω)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro ω _
    exact (OwnerRoleFiniteSource.factor G C D R hcover L Δ r k t Q T s a B q M hQ hks c v anchor mask ω).symm
  have hright : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      f (LocalSeedRecords.base l (fun j => ζ (l.get j)))) =
      ∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
          (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro ζ _
    exact OwnerRoleFiniteSource.global G C D R hcover L Δ r k t Q T s a B q M hQ hks c v anchor mask ζ
  rw [hleft, hright, ← PackedPriorityConfiguration.denominator_eq] at hm
  exact hm

theorem all_metadata {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V) :
    (∑ i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s),
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) : ℝ)) /
        (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ) =
      (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        ∑ mask : Fin ((Δ + 1) ^ k) → Bool,
          (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
            (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ)) /
              (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) : ℝ) := by
  trans (∑ mask : Fin ((Δ + 1) ^ k) → Bool,
    ∑ ω : Fin ((Δ + 1) ^ s) → PriorityPartitionBroadcast.Table Δ k Q T,
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
        (TaskRoleId.make anchor (RoleTableEncoding.pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) mask ω)) : ℝ)) /
          (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ)
  · exact congrArg (fun x : ℝ => x / (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ))
      (RoleTableEncoding.sum_pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s)
        (fun i => (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) : ℝ)))
  rw [Finset.sum_div]
  simp_rw [fixed_mask G C D R hcover L Δ r k t Q T s a B q M hQ hks c v anchor]
  rw [← Finset.sum_div, Finset.sum_comm]

end Paper.OwnerRoleConfigurationMean
