import Paper.Partitions.Local.PriorityDependence
import Paper.Preliminaries.FlatSeeds
import Paper.Partitions.Local.PriorityCut

/-! Normalize irrelevant priorities and expose an explicit finite source
indexed by stage, minimum-ID owner and a bounded local membership mask. -/
namespace Paper.PriorityNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expand (k Q : ℕ) (hQ : 0 < Q) (τ : LocalPriorityIndex.Domain G k → Fin Q)
    (U : Finset V) : Fin Q :=
  if hU : (G.induce (U : Set V)).Connected ∧ U.card ≤ k then τ ⟨U, hU⟩ else ⟨0, hQ⟩

noncomputable def coreSeed (k Q : ℕ) (hQ : 0 < Q) (n : ℕ)
    (τ : (Fin n × LocalPriorityIndex.Domain G k) → Fin Q) : FiniteIteration.Seeds (Finset V → Fin Q) n :=
  FiniteSeeds.ofFn _ n (fun t => expand G k Q hQ (fun U => τ (t, U)))

theorem ofFn_agree (k : ℕ) {Q : ℕ} (n : ℕ) (ω τ : Fin n → Finset V → Fin Q)
    (he : ∀ t, PriorityDependence.Agree G k (ω t) (τ t)) :
    PriorityDependence.SeedAgree G k n (FiniteSeeds.ofFn _ n ω) (FiniteSeeds.ofFn _ n τ) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨he 0, ih _ _ (fun t => he t.succ)⟩

theorem normalized_parts (k : ℕ) (hk : 0 < k) (ε : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (S : Finset V) (n : ℕ) (ω : (Fin n × Finset V) → Fin Q) :
    (PriorityPartition.partition G k hk ε S n (FlatSeeds.seed n ω)).parts =
      (PriorityPartition.partition G k hk ε S n
        (coreSeed G k Q hQ n (fun x => ω (x.1, x.2.val)))).parts := by
  apply PriorityDependence.parts_congr G
  apply ofFn_agree G
  intro t U
  simp only [expand, dif_pos U.property]
  rfl

theorem normalized_cut (k : ℕ) (hk : 0 < k) (ε : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (S : Finset V) (n : ℕ) (ω : (Fin n × Finset V) → Fin Q) :
    PriorityCut.cut G k hk ε S n (FlatSeeds.seed n ω) =
      PriorityCut.cut G k hk ε S n (coreSeed G k Q hQ n (fun x => ω (x.1, x.2.val))) := by
  unfold PriorityCut.cut
  rw [normalized_parts G k hk ε Q hQ S n ω]

abbrev Coordinate (V : Type*) (Δ k : ℕ) := V × (Fin ((Δ + 1) ^ k) → Bool)

noncomputable def localSeed (Δ k Q : ℕ) (hQ : 0 < Q) (n : ℕ)
    (ω : (Fin n × Coordinate V Δ k) → Fin Q) : FiniteIteration.Seeds (Finset V → Fin Q) n :=
  coreSeed G k Q hQ n (fun x => ω (x.1, LocalPriorityIndex.index G Δ k x.2))
end Paper.PriorityNormalization
