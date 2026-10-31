import Paper.Owners.Construction.OwnerValidMaskRole
import Paper.Owners.Construction.OwnerRoleScoreZero

/-! Sum every genuine part once. Invalid masks and isolated nonowner
anchors contribute exactly zero in the actual physical execution. -/
namespace Paper.OwnerMaskPartScores
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem invalid_zero {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p : OwnerMaskParts.Pair V Δ k) (hp : ¬OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ p) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 p.2 ζ) = 0 := by
  by_cases ha : p.1 ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)
  · have hv : (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).valid = false := by
      cases h : (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).valid
      · rfl
      · exact False.elim (hp ⟨ha, h⟩)
    exact OwnerRoleZero.invalid G C D R hcover L Δ r k t Q T s a B q M hQ hks c v _ hv
  · exact OwnerRoleScoreZero.outside_low G C D R hcover L Δ r k t Q T s a B q M hQ (by omega) c v p.1 ha _

theorem sum_parts {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B q M : ℕ) (c : V → Fin (B + 1)) (v : V)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    (∑ anchor : V, ∑ mask : Fin ((Δ + 1) ^ k) → Bool,
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
        (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ) / q) =
      ∑ I : ↥((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts : Set (Finset V)),
        (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
          (OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ I.val
            (I.val.min' ((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty I.val I.property))) : ℝ) / q := by
  classical
  let Valid := OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ
  let f : OwnerMaskParts.Pair V Δ k → ℝ := fun p =>
    (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 p.2 ζ) : ℝ) / q
  have hz : (∑ p : {p : OwnerMaskParts.Pair V Δ k // ¬Valid p}, f p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    dsimp only [f]
    rw [invalid_zero G C D R hcover L Δ r k t Q T s a B q M hQ hks c v ζ p.val p.property,
      Nat.cast_zero, zero_div]
  have hsum := Fintype.sum_subtype_add_sum_subtype Valid f
  rw [hz, add_zero] at hsum
  calc
    _ = ∑ p : OwnerMaskParts.Pair V Δ k, f p := (Fintype.sum_prod_type _).symm
    _ = ∑ p : {p : OwnerMaskParts.Pair V Δ k // Valid p}, f p.val := hsum.symm
    _ = _ := by
      apply Fintype.sum_equiv (OwnerMaskPartEquiv.equiv G C D R L Δ k hk t ht Q T s hQ hs ζ)
      intro p
      dsimp only [f]
      rw [OwnerValidMaskRole.minimum_role G C D R L Δ k hk t ht Q T s hQ hs ζ p.val p.property]
      rfl

end Paper.OwnerMaskPartScores
