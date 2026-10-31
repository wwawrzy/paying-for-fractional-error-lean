import Paper.Preliminaries.PhysicalListDensity
import Paper.Initialization.Pruning.InitializationFractional

/-! The mathematical initializer now follows from the physical minor-density
bound alone. Broadcast execution is still a separate dependency. -/
namespace Paper.FullInitialization
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass InitializerRun ActualInitialization
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def listParameter (a : ℝ) (f : ℕ) : ℕ :=
  Nat.ceil (a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ)) + 1

theorem parameter_pos (a : ℝ) (f : ℕ) : 1 ≤ listParameter a f := by
  dsimp [listParameter]
  omega

theorem parameter_bound (a : ℝ) (f : ℕ) :
    a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ listParameter a f := by
  have hh := Nat.le_ceil (a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ))
  unfold listParameter
  exact hh.trans (Nat.cast_le.mpr (Nat.le_succ _))

theorem integral_spec (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ O : Finset V) (hO : R₀ ⊆ covered G O) :
    let b := listParameter a (listThreshold d T)
    R₀ ⊆ covered G (InitializationCost.output G b d T R₀) ∧
      (InitializationCost.output G b d T R₀).card ≤ InitializationCost.constant b d T * O.card := by
  dsimp only
  apply InitializationCost.output_spec G _ d T (parameter_pos _ _) hd hT ha hda hTa hden R₀ O hO
  intro i
  exact PhysicalListDensity.actual_lists G _ _ _ (parameter_pos _ _) _
    (DepthOne.bound_of_minor_density G hden) ha (parameter_bound _ _)

theorem fractional_spec (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hcover : ∀ r ∈ R₀, 1 ≤ ∑ v ∈ closed G r, x v) :
    let b := listParameter a (listThreshold d T)
    R₀ ⊆ covered G (InitializationCost.output G b d T R₀) ∧
      ((InitializationCost.output G b d T R₀).card : ℝ) ≤
        InitializationCost.constant b d T * (2 * (d : ℝ) + 1) * ∑ v, x v := by
  dsimp only
  apply InitializationFractional.output_spec G _ d T (parameter_pos _ _) hd hT ha hda hTa hden R₀ x hx hcover
  intro i
  exact PhysicalListDensity.actual_lists G _ _ _ (parameter_pos _ _) _
    (DepthOne.bound_of_minor_density G hden) ha (parameter_bound _ _)

theorem weighted_spec (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V) (w x : V → ℝ)
    (hw : ∀ v, 1 ≤ w v) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R₀, 1 ≤ ∑ v ∈ closed G r, x v) :
    let b := listParameter a (listThreshold d T)
    R₀ ⊆ covered G (InitializationCost.output G b d T R₀) ∧
      ((InitializationCost.output G b d T R₀).card : ℝ) ≤
        InitializationCost.constant b d T * (2 * (d : ℝ) + 1) * ∑ v, w v * x v := by
  have hs := fractional_spec G d T hd hT ha hda hTa hden R₀ x hx hcover
  dsimp only at hs ⊢
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hsum : (∑ v, x v) ≤ ∑ v, w v * x v := by
    apply Finset.sum_le_sum
    intro v _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw v) (hx v)
  have hk : 0 ≤ (InitializationCost.constant (listParameter a (listThreshold d T)) d T : ℝ) *
      (2 * (d : ℝ) + 1) := by positivity
  exact mul_le_mul_of_nonneg_left hsum hk
end Paper.FullInitialization
