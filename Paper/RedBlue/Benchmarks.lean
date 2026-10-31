import Paper.RedBlue.Schemes
import Paper.RedBlue.Resources

/-! The supported benchmarks used by the executed programs agree with the
usual red-blue benchmarks. Isolated blue vertices never improve a cover. -/
namespace Paper.RedBlue
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem restrict_cover (R B W : Finset V)
    (hW : GeneralCoveringNormalizedIntegral.Covers (rows G R B) R W) :
    GeneralCoveringNormalizedIntegral.Covers (rows G R B) R
      (W ∩ CoveringSupport.admissible (rows G R B) R) := by
  intro r hr
  obtain ⟨v, hv, hrow⟩ := hW r hr
  exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_biUnion.mpr ⟨r, hr, hrow⟩⟩, hrow⟩

/-- A guarantee against all supported covers also applies to every blue cover,
including covers containing isolated, irrelevant blue vertices. -/
theorem all_integral_benchmarks (R B : Finset V) (c : V → ℕ)
    (z factor : ℝ) (hf : 0 ≤ factor)
    (h : ∀ W : Finset V, W ⊆ CoveringSupport.admissible (rows G R B) R →
      GeneralCoveringNormalizedIntegral.Covers (rows G R B) R W →
      z ≤ factor * ((∑ v ∈ W, c v : ℕ) : ℝ))
    (W : Finset V) (hW : GeneralCoveringNormalizedIntegral.Covers (rows G R B) R W) :
    z ≤ factor * ((∑ v ∈ W, c v : ℕ) : ℝ) := by
  have hh := h (W ∩ CoveringSupport.admissible (rows G R B) R)
    Finset.inter_subset_right (restrict_cover G R B W hW)
  have hs : (∑ v ∈ W ∩ CoveringSupport.admissible (rows G R B) R, c v) ≤
      ∑ v ∈ W, c v := Finset.sum_le_sum_of_subset Finset.inter_subset_left
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hf)

noncomputable def blueValues (R B : Finset V) (c : V → ℝ) : Set ℝ :=
  {t | ∃ x, CoveringOptimum.Feasible (rows G R B) R x ∧
    (∀ v ∉ B, x v = 0) ∧ CoveringOptimum.objective c x = t}

/-- The solver's supported LP is exactly the LP restricted to blue vertices. -/
theorem fractional_benchmark (R B : Finset V) (c : V → ℝ)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    GeneralCoveringNormalizedFractional.supportedNumber (rows G R B) R c =
      sInf (blueValues G R B c) := by
  obtain ⟨x, hx, _, hs, he⟩ :=
    CoveringSupport.exists_supported_optimum (rows G R B) R c hne hc
  have hl : IsLeast (blueValues G R B c) (CoveringOptimum.number (rows G R B) R c) := by
    refine ⟨⟨x, hx, ?_, he⟩, ?_⟩
    · intro v hv
      exact hs v (fun ha => hv (admissible_subset_blue G R B ha))
    · rintro t ⟨y, hy, _, rfl⟩
      exact GeneralCoveringNormalizedFractional.number_le_objective (rows G R B) R c hc y hy
  rw [GeneralCoveringNormalizedFractional.supportedNumber_eq_number (rows G R B) R c hne hc]
  exact hl.csInf_eq.symm

end Paper.RedBlue
#print axioms Paper.RedBlue.restrict_cover
#print axioms Paper.RedBlue.all_integral_benchmarks
#print axioms Paper.RedBlue.fractional_benchmark
#print axioms Paper.RedBlue.fractional_parameters
#print axioms Paper.RedBlue.integral_parameters
#print axioms Paper.RedBlue.integral_logarithmic_bits
#print axioms Paper.RedBlue.randomized_parameters
#print axioms Paper.RedBlue.deterministic_parameters
