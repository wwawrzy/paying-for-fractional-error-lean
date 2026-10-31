import Paper.TotalDomination.FractionalSolver
import Paper.TotalDomination.EncodedRounding
import Mathlib.Data.Finset.Sort

/-! The actual fractional solver followed by encoded total-domination rounding.
The public denominator is unchanged; the rounding caps each coordinate
locally while its guarantee charges the original fractional mass. All
numeric choices precede the graph, and no feasible vector is supplied. -/
namespace Paper.TotalDomination.NonintegerSolver
open BroadcastModel
open scoped BigOperators

def denominator {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (k b n : ℕ) : ℕ :=
  GeneralCoveringOwnerFrameAverage.denominator s.L s.Δ k b n s.q

theorem denominator_pos {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (k b n : ℕ) :
    0 < denominator s k b n := GeneralCoveringFractionalEndpoint.denominator_pos s k b n

variable {V : Type} [LinearOrder V]

/-- The projection is local and sends neither the numerator nor its denominator. -/
noncomputable def runtime {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff : ℕ) : Program V PUnit Bool :=
  .seq (FractionalSolver.runtime I s t k b n)
    (.seq (.local fun _ _ state => state.1.val)
      (EncodedRounding.program I a mu (denominator s k b n) cutoff))

theorem rounds {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff : ℕ) :
    (runtime I s t k b n a mu cutoff).rounds =
      (FractionalSolver.runtime I s t k b n).rounds + 4 := by
  simp only [runtime, Program.rounds, EncodedRounding.rounds, Nat.zero_add]

theorem maxBits {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff : ℕ) :
    (runtime I s t k b n a mu cutoff).maxBits =
      max (FractionalSolver.runtime I s t k b n).maxBits (ids + 1) := by
  have hr : (EncodedRounding.program I a mu (denominator s k b n) cutoff).maxBits =
      ids + 1 := by
    change max 0 (max 1 (max 1 (max 1 (max (ids + 1) 0)))) = ids + 1
    omega
  simp only [runtime, Program.maxBits, hr, Nat.zero_max]

noncomputable def coefficient {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (k b n c : ℕ) : ℕ :=
  max (GeneralCoveringFrameAverageResources.coefficient
    (GeneralCoveringInitializerFractional.listThreshold rho) s.L s.Δ s.A 1 k b n s.q c) (c + 1)

variable [Fintype V]

/-- Increasing labels exist for every finite linear order, including the empty one.
They are used only to relate the mathematical specification to local minima. -/
noncomputable def labels (V : Type) [Fintype V] [LinearOrder V] : V → ℕ :=
  fun v => ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val

theorem labels_strictMono : StrictMono (labels V) := by
  intro u v huv
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.strictMono huv

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (runtime I s t k b n a mu cutoff).maxBits ≤
      coefficient s k b n c * Nat.clog 2 (N + 2) := by
  have hf := GeneralCoveringFractionalEndpoint.logarithmic_bits I s t k b n
    (by decide) N c hids
  rw [maxBits]
  apply max_le
  · rw [FractionalSolver.maxBits]
    exact hf.trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · exact (logarithmic_message_budget N ids c hids).1.trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def numerator {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (v : V) : ℕ :=
  ((FractionalSolver.runtime I s t k b n).runEncoded G (fun _ => PUnit.unit) v).1.val

noncomputable def output {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff : ℕ) : Finset V :=
  Finset.univ.filter fun v => (runtime I s t k b n a mu cutoff).runEncoded G
    (fun _ => PUnit.unit) v

theorem output_eq {ids : ℕ} (I : BitCode V ids) {rho delta : ℝ}
    (s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta) (t k b n : ℕ)
    (a mu : ℚ) (cutoff : ℕ) :
    output G I s t k b n a mu cutoff =
      EncodedRounding.output G I a mu (denominator s k b n) cutoff
        (numerator G I s t k b n) := rfl

/-- One graph-uniform solver and rounding rule. The only correctness inputs
after choosing the constants are graph properties, not a vector or certificate.
The real rounding package is proof data; the runtime receives rational a, mu
and the public integer cutoff only. -/
theorem parameters (rho : ℝ) (hrho : 1 ≤ rho) (delta : ℝ) (hdelta : 0 < delta)
    (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) :
    ∃ s : GeneralCoveringFractionalErrorBudget.Parameters rho 1 delta,
      ∃ t k b n : ℕ, 0 < t ∧ 0 < k ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
        Incidence.InducedDensityBound G (a : ℝ) → ∀ {ids : ℕ} (I : BitCode V ids),
        (∀ r, ∃ v ∈ output G I s t k b n a mu (p.k + 1), G.Adj r v) ∧
          ((output G I s t k b n a mu (p.k + 1)).card : ℝ) ≤
            (2 * (a : ℝ) - (mu : ℝ)) * (1 + delta) * FractionalSolver.fractionalNumber G := by
  obtain ⟨s, t, k, b, n, ht, hk, hs⟩ := FractionalSolver.parameters rho hrho delta hdelta
  refine ⟨s, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hminor hfree hden ids I
  have hx := hs G hminor hfree I
  have hcover : ∀ r, 1 ≤ ∑ v ∈ G.neighborFinset r,
      (numerator G I s t k b n v : ℝ) / denominator s k b n := by
    simpa only [numerator, denominator, FractionalSolver.solution] using hx.2.1
  have hmass : (∑ v, (numerator G I s t k b n v : ℝ) / denominator s k b n) ≤
      (1 + delta) * FractionalSolver.fractionalNumber G := by
    simpa only [numerator, denominator, FractionalSolver.solution] using hx.2.2
  have hr := EncodedRounding.rounding_bound G I p a mu ha hmu
    (denominator s k b n) (p.k + 1) (denominator_pos s k b n) rfl
    (numerator G I s t k b n) (labels V) labels_strictMono hfree hden hcover
  rw [output_eq]
  refine ⟨hr.1, hr.2.trans ?_⟩
  have hcoef : 0 ≤ 2 * (a : ℝ) - (mu : ℝ) := by
    rw [← ha, ← hmu]
    linarith [p.a_ge_one, p.mu_le_theta, p.theta_lt_one]
  calc
    _ ≤ (2 * (a : ℝ) - (mu : ℝ)) *
        ((1 + delta) * FractionalSolver.fractionalNumber G) :=
      mul_le_mul_of_nonneg_left hmass hcoef
    _ = _ := by ring

end Paper.TotalDomination.NonintegerSolver

#print axioms Paper.TotalDomination.NonintegerSolver.output_eq
#print axioms Paper.TotalDomination.NonintegerSolver.rounds
#print axioms Paper.TotalDomination.NonintegerSolver.maxBits
#print axioms Paper.TotalDomination.NonintegerSolver.logarithmic_bits
#print axioms Paper.TotalDomination.NonintegerSolver.parameters
