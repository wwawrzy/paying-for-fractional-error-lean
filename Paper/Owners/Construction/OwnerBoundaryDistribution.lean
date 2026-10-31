import Paper.Owners.Construction.OwnerPublicProfile
import Paper.Partitions.Local.UniformPartitionDistribution
import Paper.Preliminaries.TableSourceDistribution
import Paper.Owners.Construction.OwnerRoleTaskSound

/-! Uniform graph-independent parameters give the actual public-table
boundary law. Only active low-owner IDs are charged, never isolated IDs. -/
namespace Paper.OwnerBoundaryDistribution
open scoped BigOperators

theorem parameters (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 1 ≤ L) (h : ℕ)
    (hh : 2 * a + 1 < h) (Δ t : ℕ) (ht : 0 < t) :
    ∃ k b T : ℕ, ∃ hk : 0 < k, ∃ hQ : 0 < 2 ^ b,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ D R : Finset V,
        (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T,
          ((BoundaryOwners.vertices
            (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
            (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
            (OwnerRoleTaskSound.partition G D R L Δ k hk t (2 ^ b) T hQ ζ).parts).card : ℝ)) ≤
          Fintype.card (V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T) *
            ((16 / (t : ℝ)) * (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)).card) := by
  have hpos : (0 : ℝ) < h := by linarith
  have hn : 1 ≤ h := by
    have hh' : 0 < h := by exact_mod_cast hpos
    omega
  have hC : 0 ≤ OwnerSeparator.constant a h L + 1 := by
    have hp := OwnerSeparator.constant_pos a ha h L hn hL
    linarith
  obtain ⟨k, b, T, hk, hparams⟩ := UniformPartitionDistribution.parameters
    (OwnerSeparator.constant a h L + 1) hC Δ t ht
  have hQ : 0 < 2 ^ b := pow_pos (by omega) b
  refine ⟨k, b, T, hk, hQ, ?_⟩
  intro V _ _ G _ hden D R
  letI : DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)).Adj :=
    fun _ _ => Classical.propDecidable _
  let J := PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)
  let S := PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)
  have hp := OwnerPublicProfile.spec G D R L Δ hL hden ha h hh
  have hfull := hparams J hp (PublicOwners.degree_bound G D R L Δ) S
  have hf : (∑ ω : FiniteIteration.Seeds (Finset V → Fin (2 ^ b)) T,
      (PriorityCut.cut J k hk (1 / (t : ℝ)) S T ω : ℝ)) ≤
        (Fintype.card (Finset V → Fin (2 ^ b)) : ℝ) ^ T * ((8 / (t : ℝ)) * S.card) := by
    convert hfull using 1 <;> ring
  have hcut := TableSourceDistribution.transfer J Δ (PublicOwners.degree_bound G D R L Δ)
    k hk (1 / (t : ℝ)) (2 ^ b) hQ S T ((8 / (t : ℝ)) * S.card) hf
  have hpoint : ∀ ζ : V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T,
      ((BoundaryOwners.vertices J S (OwnerRoleTaskSound.partition G D R L Δ k hk t (2 ^ b) T hQ ζ).parts).card : ℝ) ≤
      2 * (PriorityCut.cut J k hk (1 / (t : ℝ)) S T
        (PriorityNormalization.localSeed J Δ k (2 ^ b) hQ T (fun p => ζ p.2.1 (p.1, p.2.2))) : ℝ) := by
    intro ζ
    exact_mod_cast BoundaryOwners.count J S
      (OwnerRoleTaskSound.partition G D R L Δ k hk t (2 ^ b) T hQ ζ).parts
  calc
    _ ≤ ∑ ζ : V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T,
        2 * (PriorityCut.cut J k hk (1 / (t : ℝ)) S T
          (PriorityNormalization.localSeed J Δ k (2 ^ b) hQ T (fun p => ζ p.2.1 (p.1, p.2.2))) : ℝ) :=
      Finset.sum_le_sum (fun ζ _ => hpoint ζ)
    _ = 2 * ∑ ζ : V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T,
        (PriorityCut.cut J k hk (1 / (t : ℝ)) S T
          (PriorityNormalization.localSeed J Δ k (2 ^ b) hQ T (fun p => ζ p.2.1 (p.1, p.2.2))) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k (2 ^ b) T) *
        ((8 / (t : ℝ)) * S.card)) := mul_le_mul_of_nonneg_left hcut (by norm_num)
    _ = _ := by ring

end Paper.OwnerBoundaryDistribution
