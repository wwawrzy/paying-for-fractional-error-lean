import Paper.Preliminaries.LocalSourceDistribution
import Paper.Partitions.Local.PriorityPartitionBroadcast

/-! The proved partition law for flat local coordinates is exactly the
law for the actual per-owner fixed priority tables used by the program. -/
namespace Paper.TableSourceDistribution
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]

def sourceEquiv (Δ k Q T : ℕ) :
    ((Fin T × PriorityNormalization.Coordinate V Δ k) → Fin Q) ≃
      (V → PriorityPartitionBroadcast.Table Δ k Q T) where
  toFun ω v p := ω (p.1, (v, p.2))
  invFun ζ p := ζ p.2.1 (p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transfer (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (ε : ℝ)
    (Q : ℕ) (hQ : 0 < Q) (S : Finset V) (T : ℕ) (A : ℝ)
    (hfull : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) T,
      (PriorityCut.cut G k hk ε S T ω : ℝ)) ≤
      (Fintype.card (Finset V → Fin Q) : ℝ) ^ T * A) :
    (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      (PriorityCut.cut G k hk ε S T
        (PriorityNormalization.localSeed G Δ k Q hQ T (fun p => ζ p.2.1 (p.1, p.2.2))) : ℝ)) ≤
        Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q T) * A := by
  have tr := @LocalSourceDistribution.transfer V (inferInstance : Fintype V) (inferInstance : LinearOrder V)
  have hinst : (@LocalSourceDistribution.vertexEq V) =
      (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at tr
  have hflat := tr G Δ hdeg k hk ε Q hQ S T A hfull
  let f := fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
    (PriorityCut.cut G k hk ε S T
      (PriorityNormalization.localSeed G Δ k Q hQ T (fun p => ζ p.2.1 (p.1, p.2.2))) : ℝ)
  have hs : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T, f ζ) =
      ∑ ω : (Fin T × PriorityNormalization.Coordinate V Δ k) → Fin Q,
        (PriorityCut.cut G k hk ε S T (PriorityNormalization.localSeed G Δ k Q hQ T ω) : ℝ) :=
    (Fintype.sum_equiv (sourceEquiv (V := V) Δ k Q T) _ _ (fun _ => rfl)).symm
  rw [← hs] at hflat
  have hc := Fintype.card_congr (sourceEquiv (V := V) Δ k Q T)
  rw [hc] at hflat
  exact hflat

end Paper.TableSourceDistribution
