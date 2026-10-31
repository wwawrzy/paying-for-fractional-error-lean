import Paper.Partitions.Local.FinitePriorityRule
import Paper.Partitions.Local.PriorityPartition
import Paper.Partitions.Local.PriorityNormalization

/-! Pure finite priority partition kernel: actual candidate enumeration,
zero-priority selection, removal and final singleton parts. -/
namespace Paper.FinitePartition
variable {V : Type} [LinearOrder V]

def parts (N : V → Finset V) (k t : ℕ) {Q : ℕ} (S : Finset V) :
    (n : ℕ) → FiniteIteration.Seeds (Finset V → Fin Q) n → Finset (Finset V)
  | 0, _ => S.image (fun v => {v})
  | n + 1, ω =>
    FinitePriorityRule.accepted (FiniteEligibility.family N S k t) ω.1 ∪
      parts N k t (FinitePriorityRule.next N S k t ω.1) n ω.2

def source (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Q n : ℕ)
    (ω : (Fin n × (V × (Fin ((Δ + 1) ^ k) → Bool))) → Fin Q) :
    FiniteIteration.Seeds (Finset V → Fin Q) n :=
  FiniteSeeds.ofFn _ n (fun i U => ω (i, FinitePriorityIndex.index N Δ k U fallback))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) {Q : ℕ}
    (S : Finset V) (n : ℕ) (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) :
    parts (fun u => G.neighborFinset u) k t S n ω =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) S n ω).parts := by
  induction n generalizing S with
  | zero => rw [PriorityPartition.parts_zero]; rfl
  | succ n ih =>
    rw [parts, PriorityPartition.parts_succ, ih, FinitePriorityRule.next_correct G S k t ht,
      FiniteEligibility.correct G S k t ht, FinitePriorityRule.accepted_eq]

theorem canonical_correct (Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (Q : ℕ) (hQ : 0 < Q) (S : Finset V) (fallback : V) (n : ℕ)
    (ω : (Fin n × (V × (Fin ((Δ + 1) ^ k) → Bool))) → Fin Q) :
    parts (fun u => G.neighborFinset u) k t S n
      (source (fun u => G.neighborFinset u) Δ k fallback Q n ω) =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) S n
        (PriorityNormalization.localSeed G Δ k Q hQ n ω)).parts := by
  rw [correct G k hk t ht]
  have hc := PriorityDependence.parts_congr G k hk (1 / (t : ℝ)) S n
    (source (fun u => G.neighborFinset u) Δ k fallback Q n ω)
    (PriorityNormalization.localSeed G Δ k Q hQ n ω)
  have hi : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hi] at hc
  apply hc
  unfold source PriorityNormalization.localSeed PriorityNormalization.coreSeed
  apply PriorityNormalization.ofFn_agree G
  intro i U
  simp only [PriorityNormalization.expand, dif_pos U.property, FinitePriorityIndex.index_correct G Δ k U fallback]
  rfl
end Paper.FinitePartition
