import Paper.Preliminaries.ResidualFrameAgreement
import Paper.Preliminaries.FinitePartLabels

/-! Complete finite-iteration locality of root part labels. Each stage
consumes at most 3k+1 topology layers, including original priority masks. -/
namespace Paper.PartitionFrameLocality
variable {V : Type} [LinearOrder V]

def seeds (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Q n : ℕ)
    (η : Fin n → V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q) :
    FiniteIteration.Seeds (Finset V → Fin Q) n :=
  FiniteSeeds.ofFn _ n (fun i => PriorityFrameLocality.priority N Δ k fallback (η i))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem label_eq (M : V → Finset V) (F : Finset V) (x fallback : V) (Δ k t Q n : ℕ)
    (S T : Finset V)
    (η ζ : Fin n → V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) (hSF : S ⊆ F)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (n * (3 * k + 1)) ⊆ F)
    (hS : ∀ u ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (n * (3 * k + 1)), u ∈ S ↔ u ∈ T)
    (hs : ∀ i u, u ∈ F → η i u = ζ i u) :
    FinitePartLabels.label M k t S n (seeds M Δ k fallback Q n η) x =
      FinitePartLabels.label (fun u => G.neighborFinset u) k t T n
        (seeds (fun u => G.neighborFinset u) Δ k fallback Q n ζ) x := by
  induction n generalizing S T with
  | zero =>
    have he := hS x (NeighborBalls.self_mem _ x _)
    simp only [seeds, FinitePartLabels.label, he]
  | succ n ih =>
    let ρ := 3 * k + 1
    have hsmall : NeighborBalls.ball (fun u => G.neighborFinset u) x ρ ⊆
        NeighborBalls.ball (fun u => G.neighborFinset u) x ((n + 1) * ρ) :=
      NeighborBalls.monotone _ x (by nlinarith)
    have hp := ResidualFrameAgreement.part_eq G M F S T x fallback Δ k t (η 0) (ζ 0) hm hSF
      (hsmall.trans hF) (fun u hu => hS u (hsmall hu)) (fun u hu => hs 0 u hu)
    change FinitePriorityRule.part (FiniteEligibility.family M S k t)
        (PriorityFrameLocality.priority M Δ k fallback (η 0)) x ∪
        FinitePartLabels.label M k t (FinitePriorityRule.next M S k t (PriorityFrameLocality.priority M Δ k fallback (η 0)))
          n (seeds M Δ k fallback Q n (fun i => η i.succ)) x =
      FinitePriorityRule.part (FiniteEligibility.family (fun u => G.neighborFinset u) T k t)
        (PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback (ζ 0)) x ∪
        FinitePartLabels.label (fun u => G.neighborFinset u) k t
          (FinitePriorityRule.next (fun u => G.neighborFinset u) T k t (PriorityFrameLocality.priority (fun u => G.neighborFinset u) Δ k fallback (ζ 0)))
          n (seeds (fun u => G.neighborFinset u) Δ k fallback Q n (fun i => ζ i.succ)) x
    rw [hp]
    congr 1
    apply ih _ _ (fun i : Fin n => η i.succ) (fun i : Fin n => ζ i.succ)
    · exact Finset.sdiff_subset.trans hSF
    · exact (NeighborBalls.monotone _ x (by nlinarith : n * ρ ≤ (n + 1) * ρ)).trans hF
    · intro u hu
      have hb : NeighborBalls.ball (fun u => G.neighborFinset u) u ρ ⊆
          NeighborBalls.ball (fun u => G.neighborFinset u) x ((n + 1) * ρ) := by
        have hh := NeighborBalls.subball (fun u => G.neighborFinset u) (n * ρ) ρ x u hu
        simpa only [Nat.succ_mul] using hh
      exact ResidualFrameAgreement.next_iff G M F S T u fallback Δ k t (η 0) (ζ 0) hm hSF
        (hb.trans hF) (fun w hw => hS w (hb hw)) (fun w hw => hs 0 w hw)
    · exact fun i u hu => hs i.succ u hu

theorem global_math_label (Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (Q : ℕ) (hQ : 0 < Q) (S : Finset V) (fallback : V) (n : ℕ)
    (η : Fin n → V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q) (x : V) :
    FinitePartLabels.label (fun u => G.neighborFinset u) k t S n
        (seeds (fun u => G.neighborFinset u) Δ k fallback Q n η) x =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) S n
        (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => η p.1 p.2.1 p.2.2))).parts.biUnion
          (fun U => if x ∈ U then U else ∅) := by
  rw [FinitePartLabels.parts]
  change (FinitePartition.parts (fun u => G.neighborFinset u) k t S n
    (FinitePartition.source (fun u => G.neighborFinset u) Δ k fallback Q n (fun p => η p.1 p.2.1 p.2.2))).biUnion _ = _
  rw [FinitePartition.canonical_correct G Δ k hk t ht Q hQ S fallback n]

theorem local_math_label (M : V → Finset V) (F T : Finset V) (x fallback : V)
    (Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q : ℕ) (hQ : 0 < Q) (n : ℕ)
    (η ζ : Fin n → V → (Fin ((Δ + 1) ^ k) → Bool) → Fin Q)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (n * (3 * k + 1)) ⊆ F)
    (hs : ∀ i u, u ∈ F → η i u = ζ i u) :
    FinitePartLabels.label M k t (F ∩ T) n (seeds M Δ k fallback Q n η) x =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
        (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.1 p.2.1 p.2.2))).parts.biUnion
          (fun U => if x ∈ U then U else ∅) := by
  rw [label_eq G M F x fallback Δ k t Q n (F ∩ T) T η ζ hm Finset.inter_subset_left hF
    (fun u hu => ⟨fun h => (Finset.mem_inter.mp h).2, fun h => Finset.mem_inter.mpr ⟨hF hu, h⟩⟩) hs]
  exact global_math_label G Δ k hk t ht Q hQ T fallback n ζ x
end Paper.PartitionFrameLocality
