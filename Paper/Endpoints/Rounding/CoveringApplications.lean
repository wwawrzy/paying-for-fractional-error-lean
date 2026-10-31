import Paper.Endpoints.Rounding.CoveringApplicationGuarantee

/-! One deterministic covering algorithm with both approximation factors.
All numeric choices precede the graph and the original private input. -/
namespace Paper.CoveringApplications
open BroadcastModel SevenFoundation CoveringApplicationInput
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable

private theorem improve_open {a ε τ F D : ℝ} (ha : 1 ≤ a) (hε : 0 < ε)
    (hF : 0 ≤ F) (hb : F ≤ (1 + ε / (2 * a + 1)) * τ) (hD : D ≤ (2 * a) * F) :
    D ≤ (2 * a + ε) * τ := by
  have hs : 0 < 2 * a + 1 := by linarith
  have he : 0 ≤ ε / (2 * a + 1) := (div_pos hε hs).le
  have hτ : 0 ≤ τ := by
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg (by positivity : 0 < 1 + ε / (2 * a + 1)) (lt_of_not_ge hn)
    linarith
  have hcancel : (ε / (2 * a + 1)) * (2 * a + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hs)
  have hcoef : 2 * a * (1 + ε / (2 * a + 1)) ≤ 2 * a + ε := by nlinarith
  calc
    D ≤ 2 * a * F := hD
    _ ≤ 2 * a * ((1 + ε / (2 * a + 1)) * τ) := mul_le_mul_of_nonneg_left hb (by linarith)
    _ = (2 * a * (1 + ε / (2 * a + 1))) * τ := by ring
    _ ≤ (2 * a + ε) * τ := mul_le_mul_of_nonneg_right hcoef hτ

theorem parameters (ρ : ℝ) (hρ : 1 ≤ ρ) (a B : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters ρ B (ε / (2 * (a : ℝ) + 1)),
      ∃ t k b n : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G ρ → ∀ {ids : ℕ} (I : BitCode V ids) (s : V → Input V B)
        (d : GeneralCoveringInitializedFrameAverage.Original G s),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) →
        Incidence.InducedDensityBound
          (GeneralCoveringRounding.incidenceGraph G (GeneralCoveringRounding.normalize d.cover d.R)) (a : ℝ) →
        let D := Finset.univ.filter (fun v => ((program I p t k b n a hB).runEncoded G s v).selected = true)
        let τ := GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.val : ℝ))
        D ⊆ CoveringSupport.admissible d.cover d.R ∧
          (∀ r ∈ d.R, ∃ v ∈ d.cover r, v ∈ D) ∧
          (∑ v ∈ D, ((s v).2.val : ℝ)) ≤ (2 * (a : ℝ) + 1 + ε) * τ ∧
          ((∀ r ∈ d.R, r ∉ d.cover r) →
            (∑ v ∈ D, ((s v).2.val : ℝ)) ≤ (2 * (a : ℝ) + ε) * τ) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : 0 < 2 * (a : ℝ) + 1 := by linarith
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ :=
    GeneralCoveringFractionalEndpoint.parameters ρ hρ B hB (ε / (2 * (a : ℝ) + 1)) (div_pos hε hs)
  refine ⟨p, t, k, b, n, ?_⟩
  intro V _ _ G _ hG ids I s d hc hden
  obtain ⟨hf, hbudget, _⟩ := hp G hG I s d hc
  obtain ⟨hadm, hcover, hclosed, hopen⟩ :=
    CoveringApplicationGuarantee.spec G I p t k b n a ha hB s d hden hf
  dsimp only
  refine ⟨hadm, hcover, ?_, ?_⟩
  · exact CoveringApproximateRounding.scale_error hs hclosed hbudget
  · intro hself
    have hF : 0 ≤ cost (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2))
        (GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s) :=
      Finset.sum_nonneg (fun v _ => mul_nonneg (Nat.cast_nonneg _) (hf.1 v))
    exact improve_open haR hε hF hbudget (hopen hself)

end Paper.CoveringApplications

#print axioms Paper.CoveringApplications.parameters
