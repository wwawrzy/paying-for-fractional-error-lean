import Paper.Owners.Construction.OwnerProjectedRoleLP
import Paper.Owners.Construction.OwnerPublicPartition
import Paper.Averaging.Tasks.GenericOutcomeMean

/-! Proof model of the outcome formed from genuine physical role-solver
outputs, for a specified public priority source. Every part uses its
minimum-anchor projected role. No abstract task solver is selected. -/
namespace Paper.ActualRoleOutcome
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def partition (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t Q T : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :=
  OwnerPublicPartition.data G D R L (OwnerVirtualFacts.high G D R L Δ) k
    (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ)

noncomputable def partVector {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k t Q T s a B : ℕ) (hQ : 0 < Q) (ξ : ℝ) (c : V → Fin (B + 1))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (U : Finset V) (anchor v : V) : ℝ :=
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  let role := OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ U anchor
  (((TaggedDictionary.lookup (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
    (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) role).getD 0).val : ℝ) / q

noncomputable def family {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k : ℕ) (hk : 0 < k) (t Q T s a B : ℕ) (hQ : 0 < Q) (ξ : ℝ) (c : V → Fin (B + 1))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    OutcomeVector.Family G D R L (OwnerVirtualFacts.high G D R L Δ) := fun I v =>
  if hI : I ∈ (partition G D R L Δ k hk t Q T hQ ζ).parts then
    let U := PhysicalTasks.centers D (OwnerVirtualFacts.high G D R L Δ) I
    let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
    let hU := OwnerPublicPartition.public_part G D R L _ k P I hI
    partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ U (U.min' (P.nonempty U hU)) v.val
  else 0

set_option maxHeartbeats 1000000 in
theorem family_spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (I : Finset (OwnerTasks.Low D (OwnerVirtualFacts.high G D R L Δ)))
    (hI : I ∈ (partition G D R L Δ k hk t Q T hQ ζ).parts) :
    let Qlow := OwnerVirtualFacts.high G D R L Δ
    let P := partition G D R L Δ k hk t Q T hQ ζ
    let boundary := BoundaryOwners.vertices (OwnerTasks.graph G D R L Qlow) Finset.univ P.parts
    let z := family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ I
    PartialOptimum.Feasible (G.induce (PhysicalTasks.vertices G D R L Qlow I : Set V))
      (InducedSubsets.lift (PhysicalTasks.vertices G D R L Qlow I) (OwnerTasks.demands G D R L Qlow I boundary)) z ∧
      PartialOptimum.objective (fun v => ((c v.val).val : ℝ)) z ≤
        (1 + ξ) * TaskOptimum.number G D R L Qlow I boundary (fun v => ((c v).val : ℝ)) := by
  let Qlow := OwnerVirtualFacts.high G D R L Δ
  let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
  let U := PhysicalTasks.centers D Qlow I
  have hU : U ∈ P.parts := OwnerPublicPartition.public_part G D R L Qlow k P I hI
  let hn := P.nonempty U hU
  let anchor := U.min' hn
  have hanchor : anchor ∈ U := Finset.min'_mem U hn
  have hleader : FinitePriorityIndex.leader U anchor = anchor := by
    rw [FinitePriorityIndex.leader, dif_pos hn]
  have hh := OwnerProjectedRoleLP.spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a ha hden B c hc ξ hξ
    ζ U hU anchor hanchor hleader
  dsimp only at hh
  have hp : OwnerPublicTasks.pull D Qlow U = I := OwnerPublicPartition.pull_centers D Qlow I
  have hb := OwnerPublicPartition.boundary G D R L Qlow k P
  rw [hp, ← hb] at hh
  have he : family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ I =
      (fun v => partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ U anchor v.val) := by
    funext v
    unfold family
    rw [dif_pos hI]
  dsimp only
  rw [he]
  constructor
  · exact hh.1
  · exact hh.2.1

end Paper.ActualRoleOutcome
