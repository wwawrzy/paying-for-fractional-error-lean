import Paper.Partitions.Local.PriorityNormalization

/-! Exact transfer of the actual partition law to a fixed number of local
priority coordinates per owner. No independence assumption is left open. -/
namespace Paper.LocalSourceDistribution
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
local instance vertexEq : DecidableEq V := Classical.decEq _

set_option maxHeartbeats 2000000 in
theorem transfer (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (ε : ℝ)
    (Q : ℕ) (hQ : 0 < Q) (S : Finset V) (n : ℕ) (C : ℝ)
    (hfull : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      (PriorityCut.cut G k hk ε S n ω : ℝ)) ≤
      (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * C) :
    (∑ ω : (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin Q,
      (PriorityCut.cut G k hk ε S n (PriorityNormalization.localSeed G Δ k Q hQ n ω) : ℝ)) ≤
      Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin Q) * C := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  let I := LocalPriorityIndex.Domain G k
  letI : Finite I := inferInstanceAs (Finite {U : Finset V // (G.induce (U : Set V)).Connected ∧ U.card ≤ k})
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  let f : ((Fin n × I) → Fin Q) → ℝ := fun τ =>
    (PriorityCut.cut G k hk ε S n (PriorityNormalization.coreSeed G k Q hQ n τ) : ℝ)
  let e : Fin n × I → Fin n × Finset V := FlatSeeds.coordinate n (fun U : I => U.val)
  have hinj : Function.Injective e := FlatSeeds.coordinate_injective n _ Subtype.val_injective
  have hflat : (∑ ω : (Fin n × Finset V) → Fin Q, f (fun i => ω (e i))) ≤
      Fintype.card ((Fin n × Finset V) → Fin Q) * C := by
    have he : (∑ ω : (Fin n × Finset V) → Fin Q, f (fun i => ω (e i))) =
        ∑ σ : FiniteIteration.Seeds (Finset V → Fin Q) n, (PriorityCut.cut G k hk ε S n σ : ℝ) := by
      calc
        _ = ∑ ω : (Fin n × Finset V) → Fin Q,
            (PriorityCut.cut G k hk ε S n (FlatSeeds.seed n ω) : ℝ) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact congrArg (fun x : ℕ => (x : ℝ)) (PriorityNormalization.normalized_cut G k hk ε Q hQ S n ω).symm
        _ = _ := FlatSeeds.sum_seed (I := Finset V) (B := Fin Q) n
          (fun σ => (PriorityCut.cut G k hk ε S n σ : ℝ))
    rw [he]
    simpa only [FlatSeeds.card_source, Nat.cast_pow] using hfull
  have hcore := UniformProjection.reflect_bound e hinj f C hflat
  let e' : Fin n × I → Fin n × PriorityNormalization.Coordinate V Δ k :=
    FlatSeeds.coordinate n (LocalPriorityIndex.index G Δ k)
  have hinj' : Function.Injective e' := FlatSeeds.coordinate_injective n _ (LocalPriorityIndex.injective G Δ hdeg k)
  exact UniformProjection.bound e' hinj' f C hcore
end
end Paper.LocalSourceDistribution
