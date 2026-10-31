import Paper.Owners.Construction.OwnerRoleGlobalMaskMean
import Paper.Owners.Construction.OwnerMaskPartScores

/-! Exact rational output of the physical program equals the global mean
of its genuine projected-part scores, each partition part counted once. -/
namespace Paper.OwnerRoleGlobalPartMean
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B q M : ℕ) (c : V → Fin (B + 1)) (v : V) :
    (((OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val : ℝ) /
        OwnerRoleNumerator.denominator Δ k Q T s q =
      (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        ∑ I : ↥((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts : Set (Finset V)),
          (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
            (OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ I.val
              (I.val.min' ((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty I.val I.property))) : ℝ) / q) /
                (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) : ℝ) := by
  have h := congrArg (fun x : ℝ => x / q)
    (OwnerRoleGlobalMaskMean.configuration_mean G C D R hcover L Δ r k t Q T s a B q M hQ hks c v)
  have hd : (OwnerRoleNumerator.denominator Δ k Q T s q : ℝ) =
      (q : ℝ) * (Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s) : ℕ) := by
    simp only [OwnerRoleNumerator.denominator, Nat.cast_mul]
  dsimp only at h
  conv_lhs at h => rw [div_div, mul_comm _ (q : ℝ), ← hd]
  calc
    _ = _ := h
    _ = (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        ∑ anchor : V, ∑ mask : Fin ((Δ + 1) ^ k) → Bool,
          (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
            (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ) / q) /
              (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) : ℝ) := by
      rw [div_right_comm]
      congr 1
      simp only [Finset.sum_div]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ζ _
      exact OwnerMaskPartScores.sum_parts G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B q M c v ζ

end Paper.OwnerRoleGlobalPartMean
