import Paper.Solver.LocalSearch.GeneralCoveringInitializerRunBounds
import Paper.Certificates.Counting.CoveringIntegral

/-! Fractional bounds for the existing arbitrary-covering initializer.
Trimming outside the original demand set is analysis-only: it preserves the
LP and permits the integral certificate theorem's global locality interface.
The actual program still runs on its original private C-incidence input.
The cost interface explicitly requires 1 <= c everywhere and c <= B on
admissible vertices only. No optimum or orientation is a runtime input. -/
namespace Paper.GeneralCoveringInitializerFractional
open BroadcastModel SevenFoundation GeneralCoveringInitializerRun
open scoped BigOperators

noncomputable def coefficient (a : ℝ) (b h f T : ℕ) : ℝ :=
  (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) * (2 * (Nat.ceil a : ℝ) + 1)

/-- One explicit public choice. These numbers do not depend on the graph. -/
noncomputable def scale (a : ℝ) : ℕ := 2 * Nat.ceil a

noncomputable def candidateThreshold (a : ℝ) : ℕ :=
  scale a + 4 * scale a * scale a

noncomputable def listThreshold (a : ℝ) : ℕ :=
  scale a + 4 * scale a * scale a * scale a

noncomputable def listBound (a : ℝ) : ℕ :=
  max 1 (Nat.ceil (a * ((2 ^ listThreshold a + 1 : ℕ) : ℝ) ^ 4 +
    (2 ^ listThreshold a + 1 : ℕ)))

noncomputable def uniformCoefficient (a : ℝ) : ℝ :=
  coefficient a (listBound a) (candidateThreshold a) (listThreshold a) (scale a)

theorem uniform_parameters (a : ℝ) (ha : 1 ≤ a) :
    1 ≤ scale a ∧ 2 * a ≤ (scale a : ℝ) ∧ 1 ≤ listBound a ∧
      a * ((2 ^ listThreshold a + 1 : ℕ) : ℝ) ^ 4 +
        (2 ^ listThreshold a + 1 : ℕ) ≤ listBound a := by
  have hceil : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ Nat.ceil a := by exact_mod_cast ha.trans hceil
  have hs : 1 ≤ scale a := by unfold scale; omega
  have hsa : 2 * a ≤ (scale a : ℝ) := by
    unfold scale
    push_cast
    linarith
  let x : ℝ := a * ((2 ^ listThreshold a + 1 : ℕ) : ℝ) ^ 4 +
    (2 ^ listThreshold a + 1 : ℕ)
  have hxb : (Nat.ceil x : ℝ) ≤ (listBound a : ℝ) := by
    exact_mod_cast (show Nat.ceil x ≤ listBound a from le_max_right _ _)
  exact ⟨hs, hsa, le_max_left _ _, (Nat.le_ceil x).trans hxb⟩

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Only an analysis construction; it is never substituted into the program. -/
def trim (C : V → Finset V) (R : Finset V) (r : V) : Finset V :=
  if r ∈ R then C r else ∅

theorem trim_admissible (C : V → Finset V) (R : Finset V) :
    CoveringSupport.admissible (trim C R) R = CoveringSupport.admissible C R := by
  unfold CoveringSupport.admissible
  apply Finset.biUnion_congr rfl
  intro r hr
  exact if_pos hr

theorem trim_feasible (C : V → Finset V) (R : Finset V) (x : V → ℝ) :
    CoveringOptimum.Feasible (trim C R) R x ↔ CoveringOptimum.Feasible C R x := by
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨hn, ?_⟩
    intro r hr
    simpa only [trim, if_pos hr] using hf r hr
  · rintro ⟨hn, hf⟩
    refine ⟨hn, ?_⟩
    intro r hr
    simpa only [trim, if_pos hr] using hf r hr

theorem trim_values (C : V → Finset V) (R : Finset V) (c : V → ℝ) :
    CoveringOptimum.values (trim C R) R c = CoveringOptimum.values C R c := by
  ext t
  simp only [CoveringOptimum.values, Set.mem_setOf_eq, trim_feasible]

theorem trim_number (C : V → Finset V) (R : Finset V) (c : V → ℝ) :
    CoveringOptimum.number (trim C R) R c = CoveringOptimum.number C R c := by
  unfold CoveringOptimum.number
  rw [trim_values]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem trim_closed (C : V → Finset V) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) : ∀ r, trim C R r ⊆ closed G r := by
  intro r
  by_cases hr : r ∈ R
  · simpa only [trim, if_pos hr] using hlocal r hr
  · simp [trim, hr]

/-- Construct a genuine integral benchmark from the LP, with locality assumed
only on R. Orientation and fractional optima are constructed inside the
existing certificate theorem, rather than supplied as hypotheses. -/
theorem exists_benchmark (C : V → Finset V) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (c : V → ℝ) (hcOne : ∀ v, 1 ≤ c v) :
    ∃ O : Finset V, O ⊆ CoveringSupport.admissible C R ∧
      GeneralCoveringInitializerPass.Covers C R O ∧
      (O.card : ℝ) ≤ (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c ∧
      (∑ v ∈ O, c v) ≤ (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c := by
  have hn : ∀ r ∈ R, (trim C R r).Nonempty := by
    intro r hr
    simpa only [trim, if_pos hr] using hrows r hr
  obtain ⟨O, hOad, hhit, hcard, hcost⟩ := CoveringIntegral.exists_integral_optimum_cover_card G
    (trim C R) (trim_closed G C R hlocal) R hn ha (MinorDensity.induced_bound G hden)
    c (fun v => zero_le_one.trans (hcOne v)) hcOne
  rw [trim_admissible C R] at hOad
  have hO : GeneralCoveringInitializerPass.Covers C R O := by
    intro r hr
    obtain ⟨v, hv⟩ := hhit r hr
    obtain ⟨hvO, hvC⟩ := Finset.mem_inter.mp hv
    exact ⟨v, hvO, by simpa only [trim, if_pos hr] using hvC⟩
  rw [trim_number C R c] at hcard hcost
  exact ⟨O, (fun v hv => hOad v hv), hO, hcard, hcost⟩

/-- Cardinality and weighted O(tau) bounds for the actual original-C selection.
All numeric assumptions are public; no integral competitor is assumed. -/
theorem selected_bounds (C : V → Finset V) (b h f d T B : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 1 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (c : V → ℝ) (hcOne : ∀ v, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    ((selected C b h f R T).card : ℝ) ≤ coefficient a b h f T * CoveringOptimum.number C R c ∧
      (∑ v ∈ selected C b h f R T, c v) ≤
        (B : ℝ) * coefficient a b h f T * CoveringOptimum.number C R c := by
  obtain ⟨O, hOad, hO, hcard, hcost⟩ := exists_benchmark G C R hlocal hrows ha hden c hcOne
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hn := GeneralCoveringInitializerRunBounds.selected_card G C b h f d T
    hb hd hT hh hf ha0 hda hTa hden hba R O hO hlocal
  have hw := GeneralCoveringInitializerRunBounds.weighted_bound G C b h f d T B
    hb hd hT hh hf ha0 hda hTa hden hba R O hO hOad hlocal c
    (fun v hv => ⟨hcOne v, hcB v hv⟩)
  have hK : (0 : ℝ) ≤ (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) :=
    Nat.cast_nonneg _
  constructor
  · calc
      _ ≤ (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) * (O.card : ℝ) := by
        exact_mod_cast hn
      _ ≤ (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) *
          ((2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c) :=
        mul_le_mul_of_nonneg_left hcard hK
      _ = _ := by unfold coefficient; ring
  · calc
      _ ≤ (B : ℝ) * (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) *
          (∑ v ∈ O, c v) := hw
      _ ≤ (B : ℝ) * (GeneralCoveringInitializerRunBounds.constant b h f T : ℝ) *
          ((2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c) :=
        mul_le_mul_of_nonneg_left hcost (mul_nonneg (Nat.cast_nonneg B) hK)
      _ = _ := by unfold coefficient; ring

/-- Fractional guarantee for the literal private-input program, still using
the original candidates/targets and exact original C-residual at every pass. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f d T B : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 1 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ) (hcOne : ∀ v, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    GeneralCoveringInitializerPass.Covers C R (output G ids b h f T s) ∧
      output G ids b h f T s ⊆ CoveringSupport.admissible C R ∧
      ((output G ids b h f T s).card : ℝ) ≤ coefficient a b h f T * CoveringOptimum.number C R c ∧
      (∑ v ∈ output G ids b h f T s, c v) ≤
        (B : ℝ) * coefficient a b h f T * CoveringOptimum.number C R c := by
  rw [output_eq G ids C targets b h f T hb R hinc hlocal hrows s hR hC hTargets]
  have hs := selected_bounds G C b h f d T B hb hd hT hh hf ha hda hTa hden hba
    R hlocal hrows c hcOne hcB
  exact ⟨selected_covers C b h f R T hrows, selected_admissible C b h f hb R T, hs.1, hs.2⟩

/-- A graph-uniform instantiation: all program parameters depend on a alone;
B enters only the cost bound. Locality is required only for original demands. -/
theorem uniform_spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ) (hcOne : ∀ v, 1 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := output G ids (listBound a) (candidateThreshold a) (listThreshold a) (scale a) s
    GeneralCoveringInitializerPass.Covers C R D ∧
      D ⊆ CoveringSupport.admissible C R ∧
      (D.card : ℝ) ≤ uniformCoefficient a * CoveringOptimum.number C R c ∧
      (∑ v ∈ D, c v) ≤ (B : ℝ) * uniformCoefficient a * CoveringOptimum.number C R c := by
  obtain ⟨hs, hsa, hb, hba⟩ := uniform_parameters a ha
  exact spec G ids C targets (listBound a) (candidateThreshold a) (listThreshold a) (scale a)
    (scale a) B hb hs hs le_rfl le_rfl ha hsa hsa hden hba R hlocal hrows hinc c hcOne hcB
    s hR hC hTargets

end Paper.GeneralCoveringInitializerFractional

#print axioms Paper.GeneralCoveringInitializerFractional.uniform_parameters
#print axioms Paper.GeneralCoveringInitializerFractional.trim_admissible
#print axioms Paper.GeneralCoveringInitializerFractional.trim_feasible
#print axioms Paper.GeneralCoveringInitializerFractional.trim_values
#print axioms Paper.GeneralCoveringInitializerFractional.trim_number
#print axioms Paper.GeneralCoveringInitializerFractional.trim_closed
#print axioms Paper.GeneralCoveringInitializerFractional.exists_benchmark
#print axioms Paper.GeneralCoveringInitializerFractional.selected_bounds
#print axioms Paper.GeneralCoveringInitializerFractional.spec
#print axioms Paper.GeneralCoveringInitializerFractional.uniform_spec
