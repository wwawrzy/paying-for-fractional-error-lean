import Paper.RedBlue.SurfaceFractional
import Paper.RedBlue.SurfaceRounding
import Paper.RedBlue.IntegralEndpoint
import Paper.RedBlue.Feasibility

/-! Executed composition of the surface fractional solver and red-blue rounding. -/
namespace Paper.RedBlue
open BroadcastModel
open scoped BigOperators
variable {V : Type} [LinearOrder V]

noncomputable def surfaceIntegralProgram {ids M : ℕ} (I : BitCode V ids) {g : ℕ} {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :=
  CoveringSolverRounding.program I 4
    (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM)
    readRounding (fun o => o.1.val)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def surfaceIntegralOutput {ids M : ℕ} (I : BitCode V ids) {g : ℕ} {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (R B : Finset V) (c : V → Fin (M + 1)) :=
  Finset.univ.filter (fun v =>
    ((surfaceIntegralProgram I p t k b n hM).runEncoded G (solverInput G R B c) v).selected = true)

set_option maxHeartbeats 1000000 in
theorem surface_integral_output_eq {ids M : ℕ} (I : BitCode V ids) {g : ℕ} {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (R B : Finset V) (c : V → Fin (M + 1)) :
    surfaceIntegralOutput G I p t k b n hM R B c =
      CoveringThresholdCost.output G I 4
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
        (roundingInput G R B c (fun v =>
          ((GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).runEncoded G
            (solverInput G R B c) v).1.val)) := by
  unfold surfaceIntegralOutput surfaceIntegralProgram
  rw [CoveringSolverRounding.output_eq]
  rfl

theorem surface_integral_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (ε / 4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
        [DecidableRel G.Adj], (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ g) → ∀ {ids : ℕ} (I : BitCode V ids)
        (R B : Finset V), Disjoint R B → ∀ (c : V → Fin (M + 1)),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
        let D := surfaceIntegralOutput G I p t k b n hM R B c
        D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
        (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4 + ε) *
          GeneralCoveringNormalizedFractional.supportedNumber (rows G R B) R
            (fun v => ((c v).val : ℝ)) + (M : ℝ)*g := by
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ := surface_fractional_parameters g M hM (ε / 4) (by positivity)
  refine ⟨p, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hG ids I R B hRB c hne hc
  have hx := hp G hG I R B c hne hc
  let Q := GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q
  let nn := fun v => ((GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).runEncoded G
    (solverInput G R B c) v).1.val
  have hQ : 0 < Q := GeneralCoveringFractionalEndpoint.denominator_pos p k b n
  have hn : ∀ v ∉ B, nn v = 0 := by
    intro v hv
    have hz := hx.2.1 v hv
    change (nn v : ℝ) / (Q : ℝ) = 0 at hz
    rcases div_eq_zero_iff.mp hz with hz | hz
    · exact_mod_cast hz
    · have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
      linarith
  dsimp only
  rw [surface_integral_output_eq]
  refine ⟨rounding_subset_blue G I R B c nn 4 Q hQ hne hn,
    rounding_covers G I R B c nn 4 Q hne, ?_⟩
  obtain ⟨rot,hgen⟩ := hG
  have hb := surface_rounding_cost G I rot g hgen R B hRB c nn Q hQ hne hx.2.2.1
  have hf := hx.2.2.2
  change (∑ v, ((c v).val : ℝ)*((nn v : ℝ)/Q)) ≤ _ at hf
  nlinarith

end Paper.RedBlue
#print axioms Paper.RedBlue.surface_integral_output_eq
#print axioms Paper.RedBlue.surface_integral_parameters
