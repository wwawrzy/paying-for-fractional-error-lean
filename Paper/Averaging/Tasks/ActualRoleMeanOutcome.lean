import Paper.Preliminaries.ActualRoleOutcome
import Paper.Averaging.Tasks.NaturalOutcomeMean

/-! Global proof-model mean of genuine role outputs and repairs. The
only remaining distribution premise is the public boundary-count bound;
task feasibility and benchmark bounds come from the actual BC solver. -/
namespace Paper.ActualRoleMeanOutcome
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def vector {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k : ℕ) (hk : 0 < k) (t Q T s a B : ℕ) (hQ : 0 < Q) (ξ : ℝ) (c : V → Fin (B + 1)) : V → ℝ :=
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  NaturalOutcomeMean.vector G D R L (OwnerVirtualFacts.high G D R L Δ) k
    (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ)
    (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c)

set_option maxHeartbeats 1000000 in
theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    (β : ℝ) (hboundary : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      ((BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
        (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
        (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts).card : ℝ)) ≤
      Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) * β) :
    PartialOptimum.Feasible G R (vector G C D R L Δ r k hk t Q T s a B hQ ξ c) ∧
      PartialOptimum.objective (fun v => ((c v).val : ℝ))
        (vector G C D R L Δ r k hk t Q T s a B hQ ξ c) ≤
          (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) +
            B * ((HeavyRepair.heavy G D R L).card + ((OwnerVirtualFacts.high G D R L Δ).card : ℝ) + β) := by
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hb : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      ((BoundaryOwners.vertices (OwnerTasks.graph G D R L (OwnerVirtualFacts.high G D R L Δ)) Finset.univ
        (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts).card : ℝ)) ≤
        Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) * β := by
    calc
      _ = ∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
          ((BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
            (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
            (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro ζ _
        exact congrArg (fun n : ℕ => (n : ℝ)) (OwnerPublicPartition.boundary_card G D R L _ k _)
      _ ≤ _ := hboundary
  apply NaturalOutcomeMean.spec G D R hcover L (OwnerVirtualFacts.high G D R L Δ) k
    (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ)
    (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c)
    (fun v => ((c v).val : ℝ)) (fun _ => Nat.cast_nonneg _) (B : ℝ) (Nat.cast_nonneg B)
    (fun v => by dsimp only; exact_mod_cast Nat.le_of_lt_succ (c v).isLt) ξ hξ.le
  · intro ζ I hI
    exact (ActualRoleOutcome.family_spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a ha hden B c hc ξ hξ ζ I hI).1
  · intro ζ I hI
    exact (ActualRoleOutcome.family_spec G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a ha hden B c hc ξ hξ ζ I hI).2
  · exact hb

end Paper.ActualRoleMeanOutcome
