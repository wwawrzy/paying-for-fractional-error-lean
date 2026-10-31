import Paper.Solver.LocalSearch.GeneralCoveringInitializerFractional
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractional
import Paper.Solver.LocalSearch.GeneralCoveringNormalizedFractional

/-! Quantitative original supported-LP interface for the UNCHANGED actual
arbitrary-C initializer. Costs need be >=1 only on original admissible
coordinates and may be arbitrary elsewhere. extendCost is ANALYSIS-ONLY:
no runtime cost/list mutation,optimizer,benchmark or orientation input.
Public parameters/coefficient are the received InitializerFractional ones. -/
namespace Paper.GeneralCoveringInitializerSupported
open BroadcastModel SevenFoundation GeneralCoveringInitializerRun
open scoped BigOperators

/-- Explicit positivity of the existing public numeric coefficient. -/
theorem coefficient_pos (a : ℝ) (b h f T : ℕ) (hh : 0 < h) (hT : 0 < T) :
    0 < GeneralCoveringInitializerFractional.coefficient a b h f T := by
  have hn : 0 < GeneralCoveringInitializerRunBounds.constant b h f T := by
    unfold GeneralCoveringInitializerRunBounds.constant
    positivity
  unfold GeneralCoveringInitializerFractional.coefficient
  exact mul_pos (by exact_mod_cast hn) (by positivity)

theorem uniformCoefficient_pos (a : ℝ) (ha : 1 ≤ a) :
    0 < GeneralCoveringInitializerFractional.uniformCoefficient a := by
  have hs := (GeneralCoveringInitializerFractional.uniform_parameters a ha).1
  have hT : 0 < GeneralCoveringInitializerFractional.scale a := by omega
  have hh : 0 < GeneralCoveringInitializerFractional.candidateThreshold a := by
    unfold GeneralCoveringInitializerFractional.candidateThreshold
    omega
  exact coefficient_pos a (GeneralCoveringInitializerFractional.listBound a)
    (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
    (GeneralCoveringInitializerFractional.scale a) hh hT

variable {V : Type} [Fintype V] [LinearOrder V]

/-- The extension is >=1 everywhere using ONLY original admissible positivity. -/
theorem extendCost_one (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v) :
    ∀ v, 1 ≤ GeneralCoveringTaskFractional.extendCost C R c v := by
  intro v
  by_cases hv : v ∈ CoveringSupport.admissible C R
  · rw [GeneralCoveringTaskFractional.extendCost_eq C R c hv]
    exact hc v hv
  · simp only [GeneralCoveringTaskFractional.extendCost, if_neg hv, le_refl]

/-- Supported objective equality, including arbitrary negative outside costs. -/
theorem extended_objective (C : V → Finset V) (R : Finset V) (c x : V → ℝ)
    (hx : ∀ v ∉ CoveringSupport.admissible C R, x v = 0) :
    CoveringOptimum.objective (GeneralCoveringTaskFractional.extendCost C R c) x = CoveringOptimum.objective c x :=
  GeneralCoveringTaskFractional.supported_objective_congr C R _ c
    (fun _ hv => GeneralCoveringTaskFractional.extendCost_eq C R c hv) x hx

/-- SUPPORTED value sets agree; no sign or nonempty-demand premise is needed. -/
theorem supportedValues_extend (C : V → Finset V) (R : Finset V) (c : V → ℝ) :
    GeneralCoveringNormalizedFractional.supportedValues C R (GeneralCoveringTaskFractional.extendCost C R c) =
      GeneralCoveringNormalizedFractional.supportedValues C R c := by
  ext t
  constructor
  · rintro ⟨x, hx, hs, he⟩
    exact ⟨x, hx, hs, (extended_objective C R c x hs).symm.trans he⟩
  · rintro ⟨x, hx, hs, he⟩
    exact ⟨x, hx, hs, (extended_objective C R c x hs).trans he⟩

theorem supportedNumber_extend (C : V → Finset V) (R : Finset V) (c : V → ℝ) :
    GeneralCoveringNormalizedFractional.supportedNumber C R (GeneralCoveringTaskFractional.extendCost C R c) =
      GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  unfold GeneralCoveringNormalizedFractional.supportedNumber
  rw [supportedValues_extend]

/-- Extended unrestricted LP equals ORIGINAL supported LP. Nonnegativity is
required only on original admissible coordinates; outside costs are unused. -/
theorem extended_number (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v) :
    CoveringOptimum.number C R (GeneralCoveringTaskFractional.extendCost C R c) =
      GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  calc
    _ = GeneralCoveringNormalizedFractional.supportedNumber C R (GeneralCoveringTaskFractional.extendCost C R c) :=
      (GeneralCoveringNormalizedFractional.supportedNumber_eq_number C R (GeneralCoveringTaskFractional.extendCost C R c) hrows
        (GeneralCoveringTaskFractional.extendCost_nonneg C R c hc)).symm
    _ = _ := supportedNumber_extend C R c

/-- Nonnegative original supported LP for later genuine numeric budgets. -/
theorem supported_nonneg (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v) :
    0 ≤ GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  have hn := GeneralCoveringTaskFractional.extendCost_nonneg C R c hc
  obtain ⟨x, hx, he⟩ := CoveringOptimum.exists_optimum_eq_number C R (GeneralCoveringTaskFractional.extendCost C R c) hrows hn
  calc
    0 ≤ CoveringOptimum.objective (GeneralCoveringTaskFractional.extendCost C R c) x :=
      Finset.sum_nonneg (fun v _ => mul_nonneg (hn v) (hx.1 v))
    _ = CoveringOptimum.number C R (GeneralCoveringTaskFractional.extendCost C R c) := he
    _ = _ := extended_number C R c hrows hc

theorem extended_sum (C : V → Finset V) (R : Finset V) (c : V → ℝ) (W : Finset V)
    (hW : W ⊆ CoveringSupport.admissible C R) :
    (∑ v ∈ W, GeneralCoveringTaskFractional.extendCost C R c v) = ∑ v ∈ W, c v :=
  Finset.sum_congr rfl (fun v hv => GeneralCoveringTaskFractional.extendCost_eq C R c (hW hv))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact selection bits of the unchanged private-input program, encoded. -/
def output {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) (s : V → Input V) : Finset V :=
  Finset.univ.filter (fun v => ((GeneralCoveringInitializerRun.program ids b h f T).runEncoded G s v).selected = true)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) (s : V → Input V) :
    output G ids b h f T s = GeneralCoveringInitializerRun.output G ids b h f T s := by
  simp only [output, GeneralCoveringInitializerRun.output, Program.runEncoded_eq_run]

/-- Literal old selected_bounds, supplied the analysis extension, then
transported to original supported tau. The selected C-program is unchanged. -/
theorem selected_bounds (C : V → Finset V) (b h f d T B : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 1 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (c : V → ℝ)
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    ((selected C b h f R T).card : ℝ) ≤ GeneralCoveringInitializerFractional.coefficient a b h f T *
      GeneralCoveringNormalizedFractional.supportedNumber C R c ∧
    (∑ v ∈ selected C b h f R T, c v) ≤ (B : ℝ) * GeneralCoveringInitializerFractional.coefficient a b h f T *
      GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  have hs := GeneralCoveringInitializerFractional.selected_bounds G C b h f d T B hb hd hT hh hf ha hda hTa hden hba
    R hlocal hrows (GeneralCoveringTaskFractional.extendCost C R c) (extendCost_one C R c hcOne)
    (fun v hv => by rw [GeneralCoveringTaskFractional.extendCost_eq C R c hv]; exact hcB v hv)
  rw [extended_number C R c hrows (fun v hv => zero_le_one.trans (hcOne v hv))] at hs
  have he := extended_sum C R c (selected C b h f R T) (selected_admissible C b h f hb R T)
  rw [he] at hs
  exact hs

/-- Encoded original private-input guarantee with no supplied optimizer or
benchmark. Cost extension is used only while instantiating the old proof. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f d T B : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 1 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ)
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    GeneralCoveringInitializerPass.Covers C R (output G ids b h f T s) ∧
    output G ids b h f T s ⊆ CoveringSupport.admissible C R ∧
    ((output G ids b h f T s).card : ℝ) ≤ GeneralCoveringInitializerFractional.coefficient a b h f T *
      GeneralCoveringNormalizedFractional.supportedNumber C R c ∧
    (∑ v ∈ output G ids b h f T s, c v) ≤ (B : ℝ) * GeneralCoveringInitializerFractional.coefficient a b h f T *
      GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  simp only [output_eq, GeneralCoveringInitializerRun.output_eq G ids C targets b h f T hb R hinc hlocal hrows s hR hC hTargets]
  have hs := selected_bounds G C b h f d T B hb hd hT hh hf ha hda hTa hden hba R hlocal hrows c hcOne hcB
  exact ⟨selected_covers C b h f R T hrows, selected_admissible C b h f hb R T, hs.1, hs.2⟩

/-- All public program parameters and K(a) are EXACTLY the accepted choices.
Only original-R locality/admissible positivity are required. -/
theorem uniform_spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ)
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := output G ids (GeneralCoveringInitializerFractional.listBound a)
      (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
      (GeneralCoveringInitializerFractional.scale a) s
    GeneralCoveringInitializerPass.Covers C R D ∧ D ⊆ CoveringSupport.admissible C R ∧
      (D.card : ℝ) ≤ GeneralCoveringInitializerFractional.uniformCoefficient a * GeneralCoveringNormalizedFractional.supportedNumber C R c ∧
      (∑ v ∈ D, c v) ≤ (B : ℝ) * GeneralCoveringInitializerFractional.uniformCoefficient a * GeneralCoveringNormalizedFractional.supportedNumber C R c := by
  obtain ⟨hs, hsa, hb, hba⟩ := GeneralCoveringInitializerFractional.uniform_parameters a ha
  exact spec G ids C targets (GeneralCoveringInitializerFractional.listBound a)
    (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
    (GeneralCoveringInitializerFractional.scale a) (GeneralCoveringInitializerFractional.scale a) B
    hb hs hs le_rfl le_rfl ha hsa hsa hden hba R hlocal hrows hinc c hcOne hcB s hR hC hTargets

/-- Actual bounded-cost endpoint interface: the input Fin type derives the
upper cost bound; original inadmissible zero costs remain allowed. -/
theorem uniform_fin_spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → Fin (B + 1))
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (c v).val)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := output G ids (GeneralCoveringInitializerFractional.listBound a)
      (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
      (GeneralCoveringInitializerFractional.scale a) s
    GeneralCoveringInitializerPass.Covers C R D ∧ D ⊆ CoveringSupport.admissible C R ∧
      (D.card : ℝ) ≤ GeneralCoveringInitializerFractional.uniformCoefficient a *
        GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ)) ∧
      (∑ v ∈ D, ((c v).val : ℝ)) ≤ (B : ℝ) * GeneralCoveringInitializerFractional.uniformCoefficient a *
        GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ)) := by
  exact uniform_spec G ids C targets ha hden B R hlocal hrows hinc (fun v => ((c v).val : ℝ))
    (fun v hv => by
      change (1 : ℝ) ≤ ((c v).val : ℝ)
      exact_mod_cast hcOne v hv)
    (fun v _ => by
      change ((c v).val : ℝ) ≤ (B : ℝ)
      exact_mod_cast (Nat.le_of_lt_succ (c v).isLt)) s hR hC hTargets

theorem uniform_empty {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ)
    (R : Finset V) (he : R = ∅) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ)
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v) (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    output G ids (GeneralCoveringInitializerFractional.listBound a)
      (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
      (GeneralCoveringInitializerFractional.scale a) s = ∅ ∧ GeneralCoveringNormalizedFractional.supportedNumber C R c = 0 := by
  have hs := uniform_spec G ids C targets ha hden B R hlocal hrows hinc c hcOne hcB s hR hC hTargets
  dsimp only at hs
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hm := hs.2.1 hv
    simpa only [he, CoveringSupport.admissible, Finset.biUnion_empty, Finset.notMem_empty] using hm
  · rw [he]
    exact GeneralCoveringNormalizedFractional.supportedNumber_empty C c

theorem output_empty_type [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) (s : V → Input V) :
    output G ids b h f T s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v
  exact isEmptyElim v
end Paper.GeneralCoveringInitializerSupported

#print axioms Paper.GeneralCoveringInitializerSupported.coefficient_pos
#print axioms Paper.GeneralCoveringInitializerSupported.uniformCoefficient_pos
#print axioms Paper.GeneralCoveringInitializerSupported.extendCost_one
#print axioms Paper.GeneralCoveringInitializerSupported.extended_objective
#print axioms Paper.GeneralCoveringInitializerSupported.supportedValues_extend
#print axioms Paper.GeneralCoveringInitializerSupported.supportedNumber_extend
#print axioms Paper.GeneralCoveringInitializerSupported.extended_number
#print axioms Paper.GeneralCoveringInitializerSupported.supported_nonneg
#print axioms Paper.GeneralCoveringInitializerSupported.extended_sum
#print axioms Paper.GeneralCoveringInitializerSupported.output_eq
#print axioms Paper.GeneralCoveringInitializerSupported.selected_bounds
#print axioms Paper.GeneralCoveringInitializerSupported.spec
#print axioms Paper.GeneralCoveringInitializerSupported.uniform_spec
#print axioms Paper.GeneralCoveringInitializerSupported.uniform_fin_spec
#print axioms Paper.GeneralCoveringInitializerSupported.uniform_empty
#print axioms Paper.GeneralCoveringInitializerSupported.output_empty_type
