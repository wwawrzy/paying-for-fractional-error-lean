import Paper.TotalDomination.NonintegerSolver
import Paper.TotalDomination.GainAccuracy
import Paper.TotalDomination.GainParameters

/-! The two exact conclusions of `fv:total:noncrit-cor` and its exact-2a
consequence. Public configurations precede every graph, vertex type and ID
codec. The actual program starts from unit states and computes its output;
no fractional vector, labels, orientation or degree is supplied. -/
namespace Paper.TotalDomination.NonintegerEndpoint
open BroadcastModel
open scoped BigOperators

structure Config (rho a : ℚ) where
  mu : ℚ
  mu_pos : 0 < mu
  delta : ℚ
  delta_pos : 0 < delta
  solver : GeneralCoveringFractionalErrorBudget.Parameters (rho : ℝ) 1 (delta : ℝ)
  t : ℕ
  k : ℕ
  b : ℕ
  n : ℕ
  cutoff : ℕ

/-- A concrete constant independent of the graph, input and ID codec. -/
noncomputable def roundBound {rho a : ℚ} (C : Config rho a) : ℕ :=
  GeneralCoveringInitializerFractional.scale (rho : ℝ) *
      (5 + 2 * GeneralCoveringInitializerFractional.listThreshold (rho : ℝ)) +
    18 + 4 * GeneralCoveringOwnerFrameTaskInputs.outerRadius C.k C.n +
    RecursiveSearch.roundBound (4 * C.k) C.solver.A
      (GeneralCoveringTaskFractionalSolve.numeratorBound C.solver.A 1 C.k C.solver.q) + 4

noncomputable def bitsCoefficient {rho a : ℚ} (C : Config rho a) (c : ℕ) : ℕ :=
  NonintegerSolver.coefficient C.solver C.k C.b C.n c

variable {V : Type} [LinearOrder V]

noncomputable def runtime {rho a : ℚ} (C : Config rho a) {ids : ℕ} (I : BitCode V ids) :
    Program V PUnit Bool :=
  NonintegerSolver.runtime I C.solver C.t C.k C.b C.n a C.mu C.cutoff

variable [Fintype V]

theorem rounds {rho a : ℚ} (C : Config rho a) {ids : ℕ} (I : BitCode V ids) :
    (runtime C I).rounds = roundBound C := by
  unfold runtime
  rw [NonintegerSolver.rounds, FractionalSolver.rounds, GeneralCoveringFractionalEndpoint.rounds]
  rfl

theorem logarithmic_bits {rho a : ℚ} (C : Config rho a) {ids : ℕ} (I : BitCode V ids)
    (c : ℕ) (hids : ids ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (runtime C I).maxBits ≤ bitsCoefficient C c * Nat.clog 2 (Fintype.card V + 2) :=
  NonintegerSolver.logarithmic_bits I C.solver C.t C.k C.b C.n a C.mu C.cutoff
    (Fintype.card V) c hids

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The selected vertices of the actual encoded execution from unit states. -/
noncomputable def output {rho a : ℚ} (C : Config rho a) {ids : ℕ} (I : BitCode V ids) :
    Finset V :=
  Finset.univ.filter fun v => (runtime C I).runEncoded G (fun _ => PUnit.unit) v

/-- Nonnegativity follows from an attained feasible optimum, including on
the empty graph. It is not inferred from an approximation guarantee. -/
theorem fractionalNumber_nonneg (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    0 ≤ FractionalSolver.fractionalNumber G := by
  obtain ⟨x, hx, heq⟩ := CoveringOptimum.exists_optimum_eq_number
    (fun v => G.neighborFinset v) Finset.univ (fun _ => (1 : ℝ))
    (fun v _ => hfree v) (fun _ => zero_le_one)
  unfold FractionalSolver.fractionalNumber
  rw [← heq]
  change 0 ≤ ∑ v, (1 : ℝ) * x v
  exact Finset.sum_nonneg fun v _ => mul_nonneg zero_le_one (hx.1 v)

/-- All mathematical and physical-resource guarantees concern this single
actual program. The public round and bit coefficients contain no graph. -/
def Specification {rho a : ℚ} (C : Config rho a) (factor : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
    MinorDensity.Bound G (rho : ℝ) → (∀ v, (G.neighborFinset v).Nonempty) →
    Incidence.InducedDensityBound G (a : ℝ) → ∀ {ids : ℕ} (I : BitCode V ids),
      (∀ r, ∃ v ∈ output G C I, G.Adj r v) ∧
      ((output G C I).card : ℝ) ≤ factor * FractionalSolver.fractionalNumber G ∧
      (runtime C I).rounds = roundBound C ∧
      ∀ c, ids ≤ c * Nat.clog 2 (Fintype.card V + 2) →
        (runtime C I).maxBits ≤ bitsCoefficient C c * Nat.clog 2 (Fintype.card V + 2)

theorem specification_mono {rho a : ℚ} (C : Config rho a) (f g : ℝ)
    (hfg : f ≤ g) (h : Specification C f) : Specification C g := by
  intro V _ _ G _ hminor hfree hden ids I
  obtain ⟨hdom, hsize, hrounds, hbits⟩ := h G hminor hfree hden I
  exact ⟨hdom, hsize.trans (mul_le_mul_of_nonneg_right hfg (fractionalNumber_nonneg G hfree)),
    hrounds, hbits⟩

/-- The caller's chosen rational gain and accuracy are preserved exactly.
The solver constants are fixed before any graph or identifier codec. -/
theorem parameters_of_gain (rho : ℚ) (hrho : 1 ≤ rho) (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (mu : ℚ) (hmu : 0 < mu) (hmax : (mu : ℝ) ≤ Noninteger.muMax (Noninteger.gap a))
    (delta : ℚ) (hdelta : 0 < delta) :
    ∃ C : Config rho a, C.mu = mu ∧ C.delta = delta ∧
      Specification C ((2 * (a : ℝ) - (mu : ℝ)) * (1 + (delta : ℝ))) := by
  obtain ⟨p, hpa, hpmu, _, _⟩ :=
    Noninteger.parameters_of_gain_rat a ha hnoninteger mu hmu hmax
  obtain ⟨s, t, k, b, n, _, _, hs⟩ := NonintegerSolver.parameters
    (rho : ℝ) (by exact_mod_cast hrho) (delta : ℝ) (by exact_mod_cast hdelta)
    p a mu hpa hpmu
  let C : Config rho a := ⟨mu, hmu, delta, hdelta, s, t, k, b, n, p.k + 1⟩
  refine ⟨C, rfl, rfl, ?_⟩
  intro V _ _ G _ hminor hfree hden ids I
  have hactual := hs G hminor hfree hden I
  exact ⟨hactual.1, hactual.2, rounds C I, logarithmic_bits C I⟩

/-- Part (i) of `fv:total:noncrit-cor`, strengthened to any real target gain. -/
theorem parameters_below_max (rho : ℚ) (hrho : 1 ≤ rho) (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) (mu0 : ℝ)
    (hmu0 : 0 < mu0) (hbelow : mu0 < Noninteger.muMax (Noninteger.gap a)) :
    ∃ C : Config rho a, Specification C (2 * (a : ℝ) - mu0) := by
  obtain ⟨hzero, hone⟩ := Noninteger.gap_bounds a ha
    (Noninteger.noninteger_real_of_rat a hnoninteger)
  have hd : 2 ≤ 2 * (a : ℝ) := by
    have har : 1 ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  obtain ⟨mu, delta, hmu, hdelta, _, hmax, _, _, _, hcoef⟩ :=
    Noninteger.gain_accuracy_below_max (2 * (a : ℝ)) (Noninteger.gap a) mu0
      hd hzero hone hmu0 hbelow
  obtain ⟨C, _, _, hC⟩ := parameters_of_gain rho hrho a ha hnoninteger mu hmu hmax delta hdelta
  exact ⟨C, specification_mono C _ _ hcoef hC⟩

/-- Part (ii) preserves the paper's exact square-root maximum gain. -/
theorem parameters_near_max (rho : ℚ) (hrho : 1 ≤ rho) (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : Config rho a,
      Specification C (2 * (a : ℝ) - Noninteger.muMax (Noninteger.gap a) + epsilon) := by
  obtain ⟨hzero, hone⟩ := Noninteger.gap_bounds a ha
    (Noninteger.noninteger_real_of_rat a hnoninteger)
  have hd : 2 ≤ 2 * (a : ℝ) := by
    have har : 1 ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  obtain ⟨mu, delta, hmu, hdelta, hmax, _, _, _, _, _, hcoef⟩ :=
    Noninteger.gain_accuracy_near_max (2 * (a : ℝ)) (Noninteger.gap a) epsilon
      hd hzero hone hepsilon
  obtain ⟨C, _, _, hC⟩ := parameters_of_gain rho hrho a ha hnoninteger mu hmu hmax delta hdelta
  exact ⟨C, specification_mono C _ _ hcoef hC⟩

/-- The noninteger exact-2a branch follows from a positive submaximum target.
No relation between the two public densities a and rho is required. -/
theorem parameters_exact_two_a (rho : ℚ) (hrho : 1 ≤ rho) (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ C : Config rho a, Specification C (2 * (a : ℝ)) := by
  obtain ⟨hzero, hone⟩ := Noninteger.gap_bounds a ha
    (Noninteger.noninteger_real_of_rat a hnoninteger)
  have hmax := Noninteger.muMax_pos (Noninteger.gap a) hzero hone
  obtain ⟨C, hC⟩ := parameters_below_max rho hrho a ha hnoninteger
    (Noninteger.muMax (Noninteger.gap a) / 2) (by linarith) (by linarith)
  exact ⟨C, specification_mono C _ _ (by linarith) hC⟩

end Paper.TotalDomination.NonintegerEndpoint

#print axioms Paper.TotalDomination.NonintegerEndpoint.fractionalNumber_nonneg
#print axioms Paper.TotalDomination.NonintegerEndpoint.parameters_of_gain
#print axioms Paper.TotalDomination.NonintegerEndpoint.parameters_below_max
#print axioms Paper.TotalDomination.NonintegerEndpoint.parameters_near_max
#print axioms Paper.TotalDomination.NonintegerEndpoint.parameters_exact_two_a
