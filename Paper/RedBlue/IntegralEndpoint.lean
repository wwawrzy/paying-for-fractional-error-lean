import Paper.RedBlue.FractionalEndpoint
import Paper.RedBlue.Feasibility

/-! Executed composition of the planar fractional solver and red-blue rounding. -/
namespace Paper.RedBlue
open BroadcastModel
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def readRounding {M : ℕ} (s : GeneralCoveringFractionalEndpoint.Input V M) :
    CoveringThresholdInput.Input V M := ⟨s.1.residual, s.2, s.1.candidates, 0⟩

noncomputable def integralProgram {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :=
  CoveringSolverRounding.program I 4
    (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM)
    readRounding (fun o => o.1.val)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def integralOutput {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (R B : Finset V) (c : V → Fin (M + 1)) :=
  Finset.univ.filter (fun v =>
    ((integralProgram I p t k b n hM).runEncoded G (solverInput G R B c) v).selected = true)

set_option maxHeartbeats 1000000 in
theorem integral_output_eq {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (R B : Finset V) (c : V → Fin (M + 1)) :
    integralOutput G I p t k b n hM R B c =
      CoveringThresholdCost.output G I 4
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
        (roundingInput G R B c (fun v =>
          ((GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).runEncoded G
            (solverInput G R B c) v).1.val)) := by
  unfold integralOutput integralProgram
  rw [CoveringSolverRounding.output_eq]
  rfl

theorem integral_parameters (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters 3 M (ε / 4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
        [DecidableRel G.Adj], G.IsPlanar → ∀ {ids : ℕ} (I : BitCode V ids)
        (R B : Finset V), Disjoint R B → ∀ (c : V → Fin (M + 1)),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
        let D := integralOutput G I p t k b n hM R B c
        D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
        (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4 + ε) *
          GeneralCoveringNormalizedFractional.supportedNumber (rows G R B) R
            (fun v => ((c v).val : ℝ)) := by
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ := fractional_parameters M hM (ε / 4) (by positivity)
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
  rw [integral_output_eq]
  exact ⟨rounding_subset_blue G I R B c nn 4 Q hQ hne hn,
    rounding_covers G I R B c nn 4 Q hne,
    rounding_cost G I hG R B hRB c nn Q hQ hne hx.2.2.1 _ ε hx.2.2.2⟩

end Paper.RedBlue
#print axioms Paper.RedBlue.integral_output_eq
#print axioms Paper.RedBlue.integral_parameters
