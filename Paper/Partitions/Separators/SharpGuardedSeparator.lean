import Paper.Preliminaries.RouteComponents
import Paper.Partitions.Separators.SharpExcludedSeparator

/-! Lift a proved weighted physical separator to guarded route endpoints.
The remaining endpoint components inherit half-balance. -/
namespace Paper.SharpGuardedSeparator
attribute [local instance] Classical.propDecidable
open DeletionComponents HeavyComponent GuardedRoutes
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {K : SimpleGraph A} {G : SimpleGraph B} [DecidableRel K.Adj] [DecidableRel G.Adj]

theorem lift (S : System K G) (L : ℕ) (hL : ∀ v, (S.labels v).card ≤ L)
    (h : ℕ) (hh : 1 ≤ h) (hfree : G.IsKMinorFree h) :
    ∃ X : Finset A, (X.card : ℝ) ≤ (h : ℝ) ^ (3/2 : ℝ) * L * Real.sqrt (Fintype.card B) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  obtain ⟨Z, hZ, hbalance⟩ := SharpExcludedSeparator.sqrt_bound G h hh hfree
    (RouteComponents.rootWeight S) (RouteComponents.weight_nonneg S)
  rw [SharpExcludedSeparator.coefficient_eq h hh] at hZ
  refine ⟨cut S Z, ?_, RouteComponents.balanced_transfer S Z hbalance⟩
  have hc : ((cut S Z).card : ℝ) ≤ (L : ℝ) * Z.card := by exact_mod_cast cut_card S Z L hL
  calc
    _ ≤ (L : ℝ) * Z.card := hc
    _ ≤ (L : ℝ) * ((h : ℝ) ^ (3/2 : ℝ) * Real.sqrt (Fintype.card B)) :=
      mul_le_mul_of_nonneg_left hZ (Nat.cast_nonneg _)
    _ = _ := by ring

theorem proportional (S : System K G) (L : ℕ) (hL : ∀ v, (S.labels v).card ≤ L)
    (h : ℕ) (hh : 1 ≤ h) (hfree : G.IsKMinorFree h)
    (κ : ℝ) (hκ : 0 ≤ κ) (hsize : (Fintype.card B : ℝ) ≤ κ * Fintype.card A) :
    ∃ X : Finset A, (X.card : ℝ) ≤ ((h : ℝ) ^ (3/2 : ℝ) * L * Real.sqrt κ) * Real.sqrt (Fintype.card A) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  obtain ⟨X, hX, hbalanced⟩ := lift S L hL h hh hfree
  refine ⟨X, hX.trans ?_, hbalanced⟩
  have hs : Real.sqrt (Fintype.card B) ≤ Real.sqrt κ * Real.sqrt (Fintype.card A) := by
    have hh := Real.sqrt_le_sqrt hsize
    rwa [Real.sqrt_mul hκ] at hh
  have hc : 0 ≤ (h : ℝ) ^ (3/2 : ℝ) * L := by positivity
  calc
    _ ≤ ((h : ℝ) ^ (3/2 : ℝ) * L) * (Real.sqrt κ * Real.sqrt (Fintype.card A)) :=
      mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring
end Paper.SharpGuardedSeparator
