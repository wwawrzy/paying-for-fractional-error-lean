import Paper.RedBlue.SolverInput
import Paper.Optimality.Treewidth.FiveCliqueDensity

/-! The actual graph-uniform fractional solver specialized to planar red-blue
instances. Its public parameters do not depend on the graph or its degree. -/
namespace Paper.RedBlue
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem fractional_parameters (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε,
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
        [DecidableRel G.Adj], G.IsPlanar → ∀ {ids : ℕ} (I : BitCode V ids)
        (R B : Finset V) (c : V → Fin (M + 1))
        (hne : ∀ r ∈ R, (rows G R B r).Nonempty),
        (∀ v ∈ B, 1 ≤ (c v).val) →
        let x := GeneralCoveringFractionalEndpoint.solution G I p t k b n hM
          (solverInput G R B c)
        (∀ v, 0 ≤ x v) ∧ (∀ v ∉ B, x v = 0) ∧
        (∀ r ∈ R, 1 ≤ ∑ v ∈ rows G R B r, x v) ∧
        (∑ v, ((c v).val : ℝ) * x v) ≤ (1 + ε) *
          GeneralCoveringNormalizedFractional.supportedNumber (rows G R B) R
            (fun v => ((c v).val : ℝ)) := by
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ :=
    GeneralCoveringFractionalEndpoint.parameters 3 (by norm_num) M hM ε hε
  refine ⟨p, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hG ids I R B c hne hc
  have hd := FiveCliqueDensity.minor_density G hG.1
  have hs := hp G hd I (solverInput G R B c) (solverOriginal G R B c hne)
    (fun v hv => hc v (admissible_subset_blue G R B hv))
  exact ⟨hs.1.1, feasible_blue_support G R B c _ hs.1, hs.1.2.2, hs.2.1⟩

end Paper.RedBlue
#print axioms Paper.RedBlue.fractional_parameters
