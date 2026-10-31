import Paper.TotalDomination.IntegerResidualSolver
import Paper.TotalDomination.IntegerEncodedRounding
import Paper.TotalDomination.NonintegerSolver

/-! Executable integer total domination: five startup broadcasts, the actual
residual fractional solver, and four encoded rounding broadcasts. -/
namespace Paper.TotalDomination.IntegerSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

noncomputable def runtime {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :
    Program V PUnit Bool :=
  .seq (IntegerResidualSolver.runtime codec p t k b n hd)
    (.seq (.local fun _ _ s => (⟨s.2,s.1.1.val⟩ : IntegerEncodedRounding.Input V d))
      (IntegerEncodedRounding.program codec d
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)))

theorem rounds {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :
    (runtime codec p t k b n hd).rounds =
      (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).rounds+9 := by
  simp only [runtime,IntegerResidualSolver.runtime,Program.rounds,ProgramMemory.rounds,
    IntegerStartup.rounds,IntegerEncodedRounding.rounds,Nat.zero_add]
  omega

theorem maxBits {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :
    (runtime codec p t k b n hd).maxBits ≤
      max (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).maxBits (ids+1) := by
  simp only [runtime,IntegerResidualSolver.runtime,Program.maxBits,ProgramMemory.maxBits,
    IntegerStartup.maxBits,Nat.zero_max]
  exact max_le (max_le (by omega) (Nat.le_max_left _ _))
    ((IntegerEncodedRounding.maxBits codec d _).trans (Nat.le_max_right _ _))

noncomputable def coefficient {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (k b n c : ℕ) : ℕ :=
  max (GeneralCoveringFrameAverageResources.coefficient
    (GeneralCoveringInitializerFractional.listThreshold rho) p.L p.Δ p.A d k b n p.q c) (c+1)

theorem logarithmic_bits [Fintype V] {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d)
    (N c : ℕ) (hids : ids ≤ c*Nat.clog 2 (N+2)) :
    (runtime codec p t k b n hd).maxBits ≤ coefficient p k b n c*Nat.clog 2 (N+2) := by
  apply (maxBits codec p t k b n hd).trans
  apply max_le
  · exact (GeneralCoveringFractionalEndpoint.logarithmic_bits codec p t k b n hd N c hids).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · exact (logarithmic_message_budget N ids c hids).1.trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def numerator {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) (v : V) : ℕ :=
  ((IntegerResidualSolver.runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v).1.1.val

noncomputable def output {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) : Finset V :=
  Finset.univ.filter fun v => (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v

theorem run_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) = fun v =>
      decide (v ∈ IntegerSetup.finalSelection G d
        (CoveringOptimum.cap (IntegerResidualSolver.solution G codec p t k b n hd)) labels hfree) := by
  let Q := GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q
  let num := numerator G codec p t k b n hd
  have hin : (fun v => (⟨((IntegerResidualSolver.runtime codec p t k b n hd).runEncoded G
      (fun _ => PUnit.unit) v).2,num v⟩ : IntegerEncodedRounding.Input V d)) =
        IntegerEncodedRounding.localInput G d num := by
    funext v
    simp only [IntegerResidualSolver.run_eq,IntegerEncodedRounding.localInput]
  change (IntegerEncodedRounding.program codec d Q).runEncoded G
    (fun v => ⟨((IntegerResidualSolver.runtime codec p t k b n hd).runEncoded G
      (fun _ => PUnit.unit) v).2,num v⟩) = _
  rw [hin]
  exact IntegerEncodedRounding.run_eq G d Q codec num labels hmono hfree

theorem output_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    output G codec p t k b n hd = IntegerSetup.finalSelection G d
      (CoveringOptimum.cap (IntegerResidualSolver.solution G codec p t k b n hd)) labels hfree := by
  unfold output
  rw [run_eq G codec p t k b n hd labels hmono hfree]
  ext v
  simp

/-- Full integer branch: public choices precede the graph and the codec.
No feasible vector, selection, solver accuracy certificate or global sets
are supplied to the executable. -/
theorem parameters (d : ℕ) (hd : 2 ≤ d) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters ((d:ℝ)/2) d (IntegerSetup.accuracy d ((d:ℝ)/2)),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G ((d:ℝ)/2) → (∀ v, (G.neighborFinset v).Nonempty) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        (∀ r, ∃ v ∈ output G codec p t k b n (by omega), G.Adj r v) ∧
        ((output G codec p t k b n (by omega)).card : ℝ) ≤
          d*InitialSelection.totalFractionalNumber G := by
  have hε := IntegerSetup.accuracy_positive d hd (show (0:ℝ) ≤ (d:ℝ)/2 by positivity)
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := IntegerResidualSolver.parameters d hd _ hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hden hfree ids codec
  have hx := hp G hden hfree codec
  let x := CoveringOptimum.cap (IntegerResidualSolver.solution G codec p t k b n (by omega : 1 ≤ d))
  have hobj : objective G (IntegerSetup.I G d x (NonintegerSolver.labels V) hfree)
      (fun v => (IntegerSetup.c G d v : ℝ)) = ∑ v, (IntegerSetup.c G d v : ℝ)*x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    change (IntegerSetup.c G d v : ℝ)*x v = 0
    have hz : x v = 0 := hx.2.2.1 v hv
    rw [hz,mul_zero]
  have hh := IntegerSetup.exact_size G d x (NonintegerSolver.labels V) hfree hd hden
    hx.1 hx.2.1 hx.2.2.1 (by rw [hobj];exact hx.2.2.2)
  rw [output_eq G codec p t k b n (by omega) (NonintegerSolver.labels V)
    NonintegerSolver.labels_strictMono hfree]
  exact hh

end Paper.TotalDomination.IntegerSolver
#print axioms Paper.TotalDomination.IntegerSolver.parameters
#print axioms Paper.TotalDomination.IntegerSolver.logarithmic_bits
