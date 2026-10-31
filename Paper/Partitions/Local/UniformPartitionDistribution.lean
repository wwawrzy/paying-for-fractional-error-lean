import Paper.Partitions.Local.FinitePartitionDistribution

/-! Choose partition parameters BEFORE the graph. The resulting round,
priority and part-size constants are uniform in the graph's vertex count. -/
namespace Paper.UniformPartitionDistribution
open scoped BigOperators

theorem parameters (C : ℝ) (hC : 0 ≤ C) (Δ t : ℕ) (ht : 0 < t) :
    ∃ k b n : ℕ, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorProfile.Bound G C → (∀ v, G.degree v ≤ Δ) → ∀ S : Finset V,
        (∑ ω : FiniteIteration.Seeds (Finset V → Fin (2 ^ b)) n,
          (PriorityCut.cut G k hk (1 / (t : ℝ)) S n ω : ℝ)) ≤
            (8 / (t : ℝ)) * (Fintype.card (Finset V → Fin (2 ^ b)) : ℝ) ^ n * S.card := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  let ε : ℝ := 1 / t
  let η : ℝ := 8 / t
  let δ : ℝ := η / ((Δ : ℝ) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hδ : 0 < δ := by dsimp only [δ, η]; positivity
  obtain ⟨k, hk, hparam⟩ := PartitionParameters.exists_size C Δ hε
  let b := 2 * (k * 2 ^ ((Δ + 1) ^ k))
  let Q := 2 ^ b
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hsize : 2 * (k * 2 ^ ((Δ + 1) ^ k)) ≤ Q := (show b < 2 ^ b from Nat.lt_two_pow_self).le
  obtain ⟨n, hn⟩ := PriorityIteration.exists_stages Q hQ hδ
  refine ⟨k, b, n, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg S
  have hremaining := PriorityIteration.remaining G hC hprofile Δ hdeg k hk hε hparam Q hQ hsize n S
  have hr : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      ((FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card : ℝ)) ≤
      δ * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card :=
    hremaining.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) (Nat.cast_nonneg _))
  have hcut := PriorityCut.finite_mean G Δ hdeg k hk hε.le S n hr
  have he : ((Δ : ℝ) + 1) * δ = η := by dsimp only [δ]; field_simp
  have hη : η = 8 * ε := by dsimp only [η, ε]; ring
  have hcoefficient : 4 * ε + (Δ : ℝ) / 2 * δ ≤ η := by
    nlinarith [hδ.le, hε.le]
  exact hcut.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (Nat.cast_nonneg _))

end Paper.UniformPartitionDistribution
