import Paper.Initialization.Pruning.InitializationCost
import Paper.Preliminaries.WeightedIntegrality

/-! Compare the actual initializer to any feasible fractional partial cover.
The physical incidence-density transfer remains an explicit open dependency. -/
namespace Paper.InitializationFractional
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass InitializerRun ActualInitialization
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem output_spec (b d T : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hcover : ∀ r ∈ R₀, 1 ≤ ∑ v ∈ closed G r, x v)
    (hlist : ∀ i : Fin T, BoundedLists.densityHierarchy
      (lists G (candidateThreshold d T) (listThreshold d T)
        (state G b (candidateThreshold d T) (listThreshold d T) R₀ i.val)) b (listThreshold d T)) :
    R₀ ⊆ covered G (InitializationCost.output G b d T R₀) ∧
      ((InitializationCost.output G b d T R₀).card : ℝ) ≤
        InitializationCost.constant b d T * (2 * (d : ℝ) + 1) * ∑ v, x v := by
  have hdensity : ∀ S : Finset V, G.inducedEdgeCount S ≤ d * S.card := by
    intro S
    have hh := MinorDensity.induced_bound G hden S
    have hupper : a * S.card ≤ (d : ℝ) * S.card :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    have hc := hh.trans hupper
    exact_mod_cast hc
  obtain ⟨O, hO, hcost⟩ := WeightedIntegrality.exists_integral_cover G R₀ d hd hdensity
    (fun _ => 1) x (fun _ => by norm_num) hx hcover
  have hOc : (O.card : ℝ) ≤ (2 * (d : ℝ) + 1) * ∑ v, x v := by simpa using hcost
  have hs := InitializationCost.output_spec G b d T hb hd hT ha hda hTa hden R₀ O hO hlist
  refine ⟨hs.1, ?_⟩
  calc
    _ ≤ (InitializationCost.constant b d T : ℝ) * O.card := by exact_mod_cast hs.2
    _ ≤ InitializationCost.constant b d T * ((2 * (d : ℝ) + 1) * ∑ v, x v) :=
      mul_le_mul_of_nonneg_left hOc (Nat.cast_nonneg _)
    _ = _ := by ring
end Paper.InitializationFractional
