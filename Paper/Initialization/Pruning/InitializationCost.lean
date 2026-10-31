import Paper.Initialization.Pruning.ActualInitialization
import Paper.Initialization.Pruning.InitializerBenchmark

/-! Cost of the concrete initializer. The only remaining list-algorithm
structural input is the stated depth-one incidence-density hierarchy. -/
namespace Paper.InitializationCost
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass InitializerRun ActualInitialization
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem past_cost (b h f T : ℕ) (hb : 1 ≤ b) (hh : 1 ≤ h) (R₀ O : Finset V)
    (hO : R₀ ⊆ covered G O)
    (hden : ∀ i : Fin T, BoundedLists.densityHierarchy
      (lists G h f (state G b h f R₀ i.val)) b f) :
    (past G b h f R₀ T).card ≤ T * h * (BoundedLists.factor (2 * b) f + 1) * O.card := by
  rw [← past_eq_fin G b h f T R₀]
  calc
    _ ≤ ∑ i : Fin T, (selection G b h f R₀ i.val).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin T, h * (BoundedLists.factor (2 * b) f + 1) * O.card := by
      apply Finset.sum_le_sum
      intro i _
      have hR : state G b h f R₀ i.val ⊆ R₀ :=
        InitializerRun.antitone G b h f R₀ (Nat.zero_le _)
      exact InitializerBenchmark.pass_cost G b h f hb hh _ O (hR.trans hO) (hden i)
    _ = _ := by simp [mul_assoc]

noncomputable def output (b d T : ℕ) (R₀ : Finset V) : Finset V :=
  past G b (candidateThreshold d T) (listThreshold d T) R₀ T ∪
    state G b (candidateThreshold d T) (listThreshold d T) R₀ T

noncomputable def constant (b d T : ℕ) : ℕ :=
  5 * T * candidateThreshold d T * (BoundedLists.factor (2 * b) (listThreshold d T) + 1)

theorem output_spec (b d T : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ O : Finset V) (hO : R₀ ⊆ covered G O)
    (hlist : ∀ i : Fin T, BoundedLists.densityHierarchy
      (lists G (candidateThreshold d T) (listThreshold d T)
        (state G b (candidateThreshold d T) (listThreshold d T) R₀ i.val)) b (listThreshold d T)) :
    R₀ ⊆ covered G (output G b d T R₀) ∧ (output G b d T R₀).card ≤ constant b d T * O.card := by
  have hspec := ActualInitialization.output_bound G b d T hb hd hT ha hda hTa hden R₀
  refine ⟨hspec.1, ?_⟩
  have hh : 1 ≤ candidateThreshold d T := by dsimp [candidateThreshold]; omega
  have hcost := past_cost G b (candidateThreshold d T) (listThreshold d T) T hb hh R₀ O hO hlist
  have hm := Nat.mul_le_mul_left 5 hcost
  calc
    _ ≤ 5 * (past G b (candidateThreshold d T) (listThreshold d T) R₀ T).card := hspec.2
    _ ≤ 5 * (T * candidateThreshold d T * (BoundedLists.factor (2 * b) (listThreshold d T) + 1) * O.card) := hm
    _ = _ := by rw [constant]; ring
end Paper.InitializationCost
