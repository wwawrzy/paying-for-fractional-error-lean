import Paper.Endpoints.Rounding.CoveringApplicationInput

/-! Guarantees for the actual fractional-solver and mixed-rounding composition.
The only fractional premise here is instantiated by the public endpoint next. -/
namespace Paper.CoveringApplicationGuarantee
open BroadcastModel SevenFoundation CoveringApplicationInput
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n a : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s)
    (hden : Incidence.InducedDensityBound
      (GeneralCoveringRounding.incidenceGraph G (GeneralCoveringRounding.normalize d.cover d.R)) (a : ℝ))
    (hf : feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2))
      (GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s)) :
    let D := Finset.univ.filter (fun v => ((program I p t k b n a hB).runEncoded G s v).selected = true)
    let F := cost (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2))
      (GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s)
    D ⊆ CoveringSupport.admissible d.cover d.R ∧
      (∀ r ∈ d.R, ∃ v ∈ d.cover r, v ∈ D) ∧
      (∑ v ∈ D, ((s v).2.val : ℝ)) ≤ (2 * (a : ℝ) + 1) * F ∧
      ((∀ r ∈ d.R, r ∉ d.cover r) →
        (∑ v ∈ D, ((s v).2.val : ℝ)) ≤ (2 * (a : ℝ)) * F) := by
  let z := data G I p t k b n hB s
  let q := GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q
  have hq : 0 < q := GeneralCoveringFractionalEndpoint.denominator_pos p k b n
  have hi := incidence G I p t k b n hB s d
  have hl : ∀ r, (z r).demand = true → (z r).candidates ⊆ closed G r :=
    CoveringFractionalRounding.local_rows G I p t k b n hB s d
  have hr : ∀ r, (z r).demand = true → (z r).candidates.Nonempty :=
    CoveringFractionalRounding.nonempty_rows G I p t k b n hB s d
  have hc : ∀ r, (z r).demand = true →
      1 ≤ ∑ v ∈ (z r).candidates, CoveringMixedOutput.vector q z v :=
    CoveringFractionalRounding.feasible_rows G I p t k b n hB s d hf
  have hd : Incidence.InducedDensityBound
      (GeneralCoveringRounding.incidenceGraph G (CoveringMixedOutput.rows z)) (a : ℝ) := by
    simpa only [z, rows_eq G I p t k b n hB s d] using hden
  have hs : ∀ v ∉ GeneralCoveringRounding.admissible (fun r => (z r).candidates)
      (CoveringMixedOutput.demands z), CoveringMixedOutput.vector q z v = 0 := by
    intro v hv
    have hv' : v ∉ CoveringSupport.admissible d.cover d.R := by
      simpa only [z, admissible_eq G I p t k b n hB s d] using hv
    exact hf.2.1 v hv'
  dsimp only
  rw [output_eq G I p t k b n a hB s]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := CoveringMixedFeasible.admissible_output G I a q ha hq z hi hl hr hs
    simpa only [z, admissible_eq G I p t k b n hB s d] using h
  · intro r hrR
    have hdr : (z r).demand = true := by
      change (s r).1.residual = true
      rw [d.residual]
      simp [hrR]
    obtain ⟨v, hv, hm⟩ := CoveringMixedFeasible.covers G I a q ha hq z hi hl hr r hdr
    refine ⟨v, ?_, hm⟩
    change v ∈ (s r).1.candidates at hv
    simpa only [d.candidates] using hv
  · exact CoveringMixedCost.closed_cost G I a q ha hq z hi hl hr hd hc
  · intro hself
    have hselfZ : ∀ r, (z r).demand = true → r ∉ (z r).candidates := by
      intro r hdr
      change (s r).1.residual = true at hdr
      rw [d.residual, decide_eq_true_eq] at hdr
      change r ∉ (s r).1.candidates
      rw [d.candidates]
      exact hself r hdr
    exact CoveringMixedCost.open_cost G I a q ha hq z hi hl hr hd hselfZ hc

end Paper.CoveringApplicationGuarantee

#print axioms Paper.CoveringApplicationGuarantee.spec
