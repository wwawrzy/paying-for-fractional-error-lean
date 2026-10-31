import Paper.Owners.Construction.OwnerMaskParts
import Paper.Owners.Construction.OwnerProjectedRole

/-! Bijection of valid anchored masks with actual public partition parts. -/
namespace Paper.OwnerMaskPartEquiv
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_pair {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (I : Finset V)
    (hI : I ∈ (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts) :
    ∃ p : OwnerMaskParts.Pair V Δ k, OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ p ∧
      (OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p).owners = I := by
  let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
  let hn := P.nonempty I hI
  let anchor := I.min' hn
  have ha : anchor ∈ I := Finset.min'_mem I hn
  have hl : FinitePriorityIndex.leader I anchor = anchor := by
    rw [FinitePriorityIndex.leader, dif_pos hn]
  let xs := OwnerRoleInputsCorrect.canonical G D R L Δ s anchor
  let mask := FiniteSubsetCode.encode ((NeighborBalls.ball (FrameInterpreter.neighbors xs) anchor k).sort (· ≤ ·))
    ((Δ + 1) ^ k) I
  have hp := OwnerProjectedRole.spec G C D R L Δ k hk t ht Q T s hQ hs ζ I hI anchor ha hl
  exact ⟨(anchor, mask), ⟨P.subset I hI ha, hp.2.1⟩, hp.1⟩

noncomputable def equiv {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    {p : OwnerMaskParts.Pair V Δ k // OwnerMaskParts.Valid G C D R L Δ k t Q T s hQ ζ p} ≃
      {I : Finset V // I ∈ (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts} :=
  Equiv.ofBijective (fun p => ⟨(OwnerMaskParts.task G C D R L Δ k t Q T s hQ ζ p.val).owners,
    OwnerMaskParts.part G C D R L Δ k hk t ht Q T s hQ hs ζ p.val p.property⟩) ⟨by
      intro p q he
      apply Subtype.ext
      exact OwnerMaskParts.injective G C D R L Δ k hk t ht Q T s hQ hs ζ p.val q.val p.property q.property
        (congrArg Subtype.val he), by
      intro I
      obtain ⟨p, hp, he⟩ := exists_pair G C D R L Δ k hk t ht Q T s hQ hs ζ I.val I.property
      exact ⟨⟨p, hp⟩, Subtype.ext he⟩⟩

end Paper.OwnerMaskPartEquiv
