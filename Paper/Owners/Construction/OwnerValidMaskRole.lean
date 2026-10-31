import Paper.Owners.Construction.OwnerMaskPartEquiv

namespace Paper.OwnerValidMaskRole
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exact_role {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k t Q T s : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p : OwnerMaskParts.Pair V Δ k) (hp : OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ p) :
    OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 p.2 ζ =
      OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ
        (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).owners p.1 := by
  exact congrArg (fun mask => OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 mask ζ)
    (OwnerMaskParts.mask G C D R L Δ k t Q T s hQ ζ p hp)

theorem minimum_role {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p : OwnerMaskParts.Pair V Δ k) (hp : OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ p) :
    let I := (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).owners
    let hn := (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty I
      (OwnerMaskParts.part G C D R L Δ k hk t ht Q T s hQ hs ζ p hp)
    OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 p.2 ζ =
      OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ I (I.min' hn) := by
  let I := (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).owners
  let hn := (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty I
    (OwnerMaskParts.part G C D R L Δ k hk t ht Q T s hQ hs ζ p hp)
  have hh := OwnerMaskParts.leader G C D R L Δ k t Q T s hQ ζ p hp
  change FinitePriorityIndex.leader I p.1 = p.1 at hh
  rw [FinitePriorityIndex.leader, dif_pos hn] at hh
  exact (exact_role G C D R L Δ k t Q T s hQ ζ p hp).trans
    (congrArg (fun a => OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ I a) hh.symm)

end Paper.OwnerValidMaskRole
