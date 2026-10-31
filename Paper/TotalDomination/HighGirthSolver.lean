import Paper.TotalDomination.HighGirthResidualSolver
import Paper.TotalDomination.HighGirthEncodedRounding
import Paper.TotalDomination.NonintegerSolver

/-! Executable integer total domination: five startup broadcasts, the actual
residual fractional solver, and four encoded rounding broadcasts. -/
namespace Paper.TotalDomination.HighGirthSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

noncomputable def runtime {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :
    Program V PUnit Bool :=
  .seq (HighGirthResidualSolver.runtime codec p t k b n hd)
    (.seq (.local fun _ _ s => (⟨s.2,s.1.1.val⟩ : HighGirthEncodedRounding.Input V))
      (HighGirthEncodedRounding.program codec
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)))

theorem rounds {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :
    (runtime codec p t k b n hd).rounds =
      (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).rounds+9 := by
  simp only [runtime,HighGirthResidualSolver.runtime,Program.rounds,ProgramMemory.rounds,
    HighGirthStartup.rounds,HighGirthEncodedRounding.rounds,Nat.zero_add]
  omega

theorem maxBits {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :
    (runtime codec p t k b n hd).maxBits ≤
      max (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).maxBits (ids+1) := by
  simp only [runtime,HighGirthResidualSolver.runtime,Program.maxBits,ProgramMemory.maxBits,
    HighGirthStartup.maxBits,Nat.zero_max]
  exact max_le (max_le (by omega) (Nat.le_max_left _ _))
    ((HighGirthEncodedRounding.maxBits codec _).trans (Nat.le_max_right _ _))

noncomputable def coefficient {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (k b n c : ℕ) : ℕ :=
  max (GeneralCoveringFrameAverageResources.coefficient
    (GeneralCoveringInitializerFractional.listThreshold rho) p.L p.Δ p.A 2 k b n p.q c) (c+1)

theorem logarithmic_bits [Fintype V] {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2)
    (N c : ℕ) (hids : ids ≤ c*Nat.clog 2 (N+2)) :
    (runtime codec p t k b n hd).maxBits ≤ coefficient p k b n c*Nat.clog 2 (N+2) := by
  apply (maxBits codec p t k b n hd).trans
  apply max_le
  · exact (GeneralCoveringFractionalEndpoint.logarithmic_bits codec p t k b n hd N c hids).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · exact (logarithmic_message_budget N ids c hids).1.trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def finalSelection (x : V → ℝ) (labels : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) : Finset V :=
  HighGirthSetup.F G ∪ HighGirthSetup.selected G x labels hfree

noncomputable def numerator {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) (v : V) : ℕ :=
  ((HighGirthResidualSolver.runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v).1.1.val

noncomputable def output {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) : Finset V :=
  Finset.univ.filter fun v => (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v

theorem run_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) = fun v =>
      decide (v ∈ finalSelection G
        (CoveringOptimum.cap (HighGirthResidualSolver.solution G codec p t k b n hd)) labels hfree) := by
  let Q := GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q
  let num := numerator G codec p t k b n hd
  have hin : (fun v => (⟨((HighGirthResidualSolver.runtime codec p t k b n hd).runEncoded G
      (fun _ => PUnit.unit) v).2,num v⟩ : HighGirthEncodedRounding.Input V)) =
        HighGirthEncodedRounding.localInput G num := by
    funext v
    simp only [HighGirthResidualSolver.run_eq,HighGirthEncodedRounding.localInput]
  change (HighGirthEncodedRounding.program codec Q).runEncoded G
    (fun v => ⟨((HighGirthResidualSolver.runtime codec p t k b n hd).runEncoded G
      (fun _ => PUnit.unit) v).2,num v⟩) = _
  rw [hin]
  exact HighGirthEncodedRounding.run_eq G Q codec num labels hmono hfree

theorem output_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    output G codec p t k b n hd = finalSelection G
      (CoveringOptimum.cap (HighGirthResidualSolver.solution G codec p t k b n hd)) labels hfree := by
  unfold output
  rw [run_eq G codec p t k b n hd labels hmono hfree]
  ext v
  simp

theorem parameters (rho a : ℝ) (hrho : 1 ≤ rho) (ha : 1 ≤ a) (hhi : a < 9/8) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 (HighGirthSlackArithmetic.accuracy a),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
        Incidence.InducedDensityBound G a → ∀ {ids : ℕ} (codec : BitCode V ids),
        (∀ r, ∃ v ∈ output G codec p t k b n (by norm_num), G.Adj r v) ∧
        ((output G codec p t k b n (by norm_num)).card : ℝ) ≤
          2*HighGirthSelection.totalFractionalNumber G := by
  have hε := HighGirthSlackArithmetic.accuracy_positive a ha hhi
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := HighGirthResidualSolver.parameters_general rho hrho _ hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hminor hfree hden ids codec
  have hx := hp G hminor hfree codec
  let x := CoveringOptimum.cap (HighGirthResidualSolver.solution G codec p t k b n (by norm_num : 1 ≤ 2))
  have hobj : objective G (HighGirthSetup.I G x (NonintegerSolver.labels V) hfree)
      (fun v => (HighGirthSetup.c G v : ℝ)) = ∑ v, (HighGirthSetup.c G v : ℝ)*x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    change (HighGirthSetup.c G v : ℝ)*x v = 0
    have hz : x v = 0 := hx.2.2.1 v hv
    rw [hz,mul_zero]
  have hh := HighGirthSetup.coefficient_two G x (NonintegerSolver.labels V) hfree a ha hhi hden
    hx.1 hx.2.1 hx.2.2.1 (by rw [hobj];exact hx.2.2.2)
  rw [output_eq G codec p t k b n (by norm_num) (NonintegerSolver.labels V)
    NonintegerSolver.labels_strictMono hfree]
  exact hh
end Paper.TotalDomination.HighGirthSolver
#print axioms Paper.TotalDomination.HighGirthSolver.parameters
#print axioms Paper.TotalDomination.HighGirthSolver.logarithmic_bits
