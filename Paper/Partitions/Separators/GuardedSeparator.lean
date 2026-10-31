import Paper.Preliminaries.RouteComponents
import Paper.Partitions.Separators.WeightedSeparator

/-! Lift a proved weighted physical separator to guarded route endpoints.
The remaining endpoint components inherit half-balance. -/
namespace Paper.GuardedSeparator
attribute [local instance] Classical.propDecidable
open DeletionComponents HeavyComponent GuardedRoutes
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {K : SimpleGraph A} {G : SimpleGraph B} [DecidableRel K.Adj] [DecidableRel G.Adj]

theorem lift (S : System K G) (L : ℕ) (hL : ∀ v, (S.labels v).card ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    ∃ X : Finset A, (X.card : ℝ) ≤ 2 * (h : ℝ) ^ 2 * L * Real.sqrt (Fintype.card B) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  obtain ⟨Z, hZ, hbalance⟩ := WeightedSeparator.sqrt_bound G hden ha h hh
    (RouteComponents.rootWeight S) (RouteComponents.weight_nonneg S)
  refine ⟨cut S Z, ?_, RouteComponents.balanced_transfer S Z hbalance⟩
  have hc : ((cut S Z).card : ℝ) ≤ (L : ℝ) * Z.card := by exact_mod_cast cut_card S Z L hL
  calc
    _ ≤ (L : ℝ) * Z.card := hc
    _ ≤ (L : ℝ) * (2 * (h : ℝ) ^ 2 * Real.sqrt (Fintype.card B)) :=
      mul_le_mul_of_nonneg_left hZ (Nat.cast_nonneg _)
    _ = _ := by ring

theorem proportional (S : System K G) (L : ℕ) (hL : ∀ v, (S.labels v).card ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h)
    (κ : ℝ) (hκ : 0 ≤ κ) (hsize : (Fintype.card B : ℝ) ≤ κ * Fintype.card A) :
    ∃ X : Finset A, (X.card : ℝ) ≤ (2 * (h : ℝ) ^ 2 * L * Real.sqrt κ) * Real.sqrt (Fintype.card A) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  obtain ⟨X, hX, hbalanced⟩ := lift S L hL hden ha h hh
  refine ⟨X, hX.trans ?_, hbalanced⟩
  have hs : Real.sqrt (Fintype.card B) ≤ Real.sqrt κ * Real.sqrt (Fintype.card A) := by
    have hh := Real.sqrt_le_sqrt hsize
    rwa [Real.sqrt_mul hκ] at hh
  have hc : 0 ≤ 2 * (h : ℝ) ^ 2 * L := by positivity
  calc
    _ ≤ (2 * (h : ℝ) ^ 2 * L) * (Real.sqrt κ * Real.sqrt (Fintype.card A)) :=
      mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring
end Paper.GuardedSeparator
