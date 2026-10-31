import Paper.Owners.Construction.OwnerProjectedMaskSound
import Paper.Averaging.Tasks.RoleTaskCanonical

/-! A valid anchored mask identifies exactly one part of the specified
global priority partition, with canonical minimum anchor and subset mask. -/
namespace Paper.OwnerMaskParts
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Pair (V : Type) (Δ k : ℕ) := V × (Fin ((Δ + 1) ^ k) → Bool)

noncomputable def task {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ k t Q T s : ℕ) (hQ : 0 < Q)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (p : Pair V Δ k) :=
  OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ
    (OwnerRoleFiniteSource.role G D R L Δ k Q T s hQ p.1 p.2 ζ)

def Valid {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ k t Q T s : ℕ) (hQ : 0 < Q)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (p : Pair V Δ k) : Prop :=
  p.1 ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ) ∧
    (task G C D R L Δ k t Q T s hQ ζ p).valid = true

noncomputable local instance validDec {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k t Q T s : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    DecidablePred (Valid G C D R L Δ k t Q T s hQ ζ) := fun _ => Classical.propDecidable _

theorem part {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (p : Pair V Δ k)
    (hp : Valid G C D R L Δ k t Q T s hQ ζ p) :
    (task G C D R L Δ k t Q T s hQ ζ p).owners ∈
      (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts :=
  (OwnerProjectedMaskSound.sound G C D R L Δ k hk t ht Q T s hQ hs p.1 hp.1 p.2 ζ hp.2).1

theorem mask {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k t Q T s : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p : Pair V Δ k) (hp : Valid G C D R L Δ k t Q T s hQ ζ p) :
    p.2 = FiniteSubsetCode.encode
      ((NeighborBalls.ball (FrameInterpreter.neighbors (OwnerRoleInputsCorrect.canonical G D R L Δ s p.1)) p.1 k).sort (· ≤ ·))
      ((Δ + 1) ^ k) (task G C D R L Δ k t Q T s hQ ζ p).owners := by
  have hh := RoleTaskCanonical.mask C Δ k t Q T ((Δ + 1) ^ s) hQ p.1
    (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ
      (OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D R L Δ s p.1)) ζ p.2)
    (OwnerRoleInputsCorrect.canonical G D R L Δ s p.1) hp.2
  rw [OwnerRoleConfigProjection.mask_project] at hh
  exact hh

theorem leader {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k t Q T s : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p : Pair V Δ k) (hp : Valid G C D R L Δ k t Q T s hQ ζ p) :
    FinitePriorityIndex.leader (task G C D R L Δ k t Q T s hQ ζ p).owners p.1 = p.1 :=
  RoleTaskCanonical.leader C Δ k t Q T ((Δ + 1) ^ s) hQ p.1 _ _ hp.2

theorem anchor_unique (S T : Finset V) (hS : S.Nonempty) (he : S = T) (a b : V)
    (ha : FinitePriorityIndex.leader S a = a) (hb : FinitePriorityIndex.leader T b = b) : a = b := by
  subst T
  rw [FinitePriorityIndex.leader, dif_pos hS] at ha hb
  exact ha.symm.trans hb

theorem injective {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (p q : Pair V Δ k) (hp : Valid G C D R L Δ k t Q T s hQ ζ p)
    (hq : Valid G C D R L Δ k t Q T s hQ ζ q)
    (he : (task G C D R L Δ k t Q T s hQ ζ p).owners = (task G C D R L Δ k t Q T s hQ ζ q).owners) : p = q := by
  have hn := (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty _
    (part G C D R L Δ k hk t ht Q T s hQ hs ζ p hp)
  have ha := anchor_unique _ _ hn he p.1 q.1 (leader G C D R L Δ k t Q T s hQ ζ p hp)
    (leader G C D R L Δ k t Q T s hQ ζ q hq)
  apply Prod.ext ha
  have hm := mask G C D R L Δ k t Q T s hQ ζ p hp
  rw [ha, he] at hm
  exact hm.trans (mask G C D R L Δ k t Q T s hQ ζ q hq).symm

end Paper.OwnerMaskParts
