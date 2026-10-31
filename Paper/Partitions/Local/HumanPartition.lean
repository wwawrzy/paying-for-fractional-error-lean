import Paper.Partitions.Separators.SeparatorBalance
import Paper.Partitions.Local.UniformPartitionDistribution
import Paper.Preliminaries.LocalSourceDistribution

/-! The paper assumes two-thirds separators, while the implementation
uses half-balanced profiles. This theorem proves the conversion and chooses
all finite-priority bounds before the graph. -/
namespace Paper.HumanPartition
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem parameters (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C (2/3) → (∀ v, G.degree v ≤ Δ) → ∀ S : Finset V,
          (∑ ω : (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2^b),
            (PriorityCut.cut G k hk (1/(t : ℝ)) S n
              (PriorityNormalization.localSeed G Δ k (2^b) (by positivity) n ω) : ℝ)) ≤
            η*Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2^b))*S.card := by
  let t := Nat.ceil (8/η)+1
  have ht : 0 < t := by dsimp [t]; omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hbound : 8/(t : ℝ) ≤ η := by
    have hceil := Nat.le_ceil (8/η)
    have hh : 8/η ≤ (t : ℝ) := hceil.trans (by dsimp [t]; push_cast; linarith)
    have hp := (div_le_iff₀ hη).mp hh
    exact (div_le_iff₀ htR).mpr (by nlinarith)
  obtain ⟨k, b, n, hk, hparams⟩ := UniformPartitionDistribution.parameters (2*C) (by positivity) Δ t ht
  refine ⟨t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg S
  classical
  let Q := 2^b
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hfull := hparams G (SeparatorBalance.half_profile G hC hprofile) hdeg S
  have hf : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      (PriorityCut.cut G k hk (1/(t : ℝ)) S n ω : ℝ)) ≤
        (Fintype.card (Finset V → Fin Q) : ℝ)^n*(η*S.card) := by
    calc
      _ ≤ (8/(t : ℝ))*(Fintype.card (Finset V → Fin Q) : ℝ)^n*S.card := hfull
      _ ≤ η*(Fintype.card (Finset V → Fin Q) : ℝ)^n*S.card := by gcongr
      _ = _ := by ring
  have hh := LocalSourceDistribution.transfer G Δ hdeg k hk (1/(t : ℝ)) Q hQ S n (η*S.card) hf
  nlinarith

end Paper.HumanPartition
