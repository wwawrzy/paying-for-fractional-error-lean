import Paper.Preliminaries.ActualRoleOutcome
import Paper.Owners.Construction.OwnerProjectedScoreOutside

/-! A projected part score is exactly its zero-extended genuine induced
task vector, including vertices outside the task's physical graph. -/
namespace Paper.ActualRoleTaskExtension
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem minimum_congr (f : Finset V → V → ℝ) (S T : Finset V)
    (hS : S.Nonempty) (hT : T.Nonempty) (he : S = T) : f S (S.min' hS) = f T (T.min' hT) := by
  subst T
  rfl

theorem part {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B : ℕ) (ξ : ℝ) (c : V → Fin (B + 1))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (U : Finset V)
    (hU : U ∈ (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts) (v : V) :
    let Qlow := OwnerVirtualFacts.high G D R L Δ
    let I := OwnerPublicTasks.pull D Qlow U
    InducedExtension.extend (PhysicalTasks.vertices G D R L Qlow I)
      (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ I) v =
      ActualRoleOutcome.partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ U
        (U.min' ((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty U hU)) v := by
  let Qlow := OwnerVirtualFacts.high G D R L Δ
  let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
  let I := OwnerPublicTasks.pull D Qlow U
  let hn := P.nonempty U hU
  let anchor := U.min' hn
  have ha : anchor ∈ U := Finset.min'_mem U hn
  have hl : FinitePriorityIndex.leader U anchor = anchor := by
    rw [FinitePriorityIndex.leader, dif_pos hn]
  have hI : I ∈ (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts :=
    Finset.mem_image.mpr ⟨U, hU, rfl⟩
  have hc := OwnerPublicTasks.centers D Qlow U (P.subset U hU)
  change PhysicalTasks.centers D Qlow I = U at hc
  have hf : ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ I =
      (fun w => ActualRoleOutcome.partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ U anchor w.val) := by
    funext w
    unfold ActualRoleOutcome.family
    rw [dif_pos hI]
    exact minimum_congr (fun (S : Finset V) (root : V) => ActualRoleOutcome.partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ S root w.val)
      _ U (hc.symm ▸ hn) hn hc
  dsimp only
  rw [hf]
  unfold InducedExtension.extend
  by_cases hv : v ∈ PhysicalTasks.vertices G D R L Qlow I
  · rw [dif_pos hv]
  · rw [dif_neg hv]
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    change 0 = (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ U anchor) : ℝ) / q
    rw [OwnerProjectedScoreOutside.zero G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B q M c ζ U hU anchor ha hl v hv,
      Nat.cast_zero, zero_div]

end Paper.ActualRoleTaskExtension
