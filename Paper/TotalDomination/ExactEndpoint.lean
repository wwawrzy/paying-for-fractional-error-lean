import Paper.TotalDomination.IntegerSolver
import Paper.TotalDomination.NonintegerEndpoint

/-! Both parts of fv:total:exact as actual graph-uniform algorithms. -/
namespace Paper.TotalDomination.ExactEndpoint
open BroadcastModel

structure Algorithm where
  runtime : {V : Type} → [LinearOrder V] → {ids : ℕ} → BitCode V ids → Program V PUnit Bool
  roundBound : ℕ
  bitsCoefficient : ℕ → ℕ

variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def output (A : Algorithm) {ids : ℕ} (codec : BitCode V ids) : Finset V :=
  Finset.univ.filter fun v => (A.runtime codec).runEncoded G (fun _ => PUnit.unit) v

def Outcome (A : Algorithm) (a : ℚ) {ids : ℕ} (codec : BitCode V ids) : Prop :=
  (∀ r, ∃ v ∈ output G A codec, G.Adj r v) ∧
  ((output G A codec).card : ℝ) ≤ 2*(a:ℝ)*FractionalSolver.fractionalNumber G ∧
  (A.runtime codec).rounds = A.roundBound ∧
  ∀ c, ids ≤ c*Nat.clog 2 (Fintype.card V+2) →
    (A.runtime codec).maxBits ≤ A.bitsCoefficient c*Nat.clog 2 (Fintype.card V+2)

noncomputable def nonintegerAlgorithm {rho a : ℚ} (C : NonintegerEndpoint.Config rho a) : Algorithm where
  runtime := fun codec => NonintegerEndpoint.runtime C codec
  roundBound := NonintegerEndpoint.roundBound C
  bitsCoefficient := NonintegerEndpoint.bitsCoefficient C

/-- Full part (ii), with public constants before graph and ID codec. -/
theorem subgraph_parameters (rho a : ℚ) (ha : 1 ≤ a) (harho : a ≤ rho)
    (hnoninteger : ¬ ∃ z : ℤ, (z:ℚ) = 2*a) :
    ∃ A : Algorithm, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G (rho:ℝ) → (∀ v, (G.neighborFinset v).Nonempty) →
      Incidence.InducedDensityBound G (a:ℝ) → ∀ {ids : ℕ} (codec : BitCode V ids),
      Outcome G A a codec := by
  obtain ⟨C,hC⟩ := NonintegerEndpoint.parameters_exact_two_a rho (ha.trans harho) a ha hnoninteger
  refine ⟨nonintegerAlgorithm C,?_⟩
  intro V _ _ G _ hden hfree hsub ids codec
  exact hC G hden hfree hsub codec

noncomputable def integerRoundBound {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ((d:ℝ)/2) d (IntegerSetup.accuracy d ((d:ℝ)/2)))
    (k n : ℕ) : ℕ :=
  GeneralCoveringInitializerFractional.scale ((d:ℝ)/2)*
      (5+2*GeneralCoveringInitializerFractional.listThreshold ((d:ℝ)/2))+
    18+4*GeneralCoveringOwnerFrameTaskInputs.outerRadius k n+
    RecursiveSearch.roundBound (4*k) p.A (GeneralCoveringTaskFractionalSolve.numeratorBound p.A d k p.q)+9

noncomputable def integerAlgorithm {d : ℕ} (hd : 1 ≤ d)
    (p : GeneralCoveringFractionalErrorBudget.Parameters ((d:ℝ)/2) d (IntegerSetup.accuracy d ((d:ℝ)/2)))
    (t k b n : ℕ) : Algorithm where
  runtime := fun codec => IntegerSolver.runtime codec p t k b n hd
  roundBound := integerRoundBound p k n
  bitsCoefficient := IntegerSolver.coefficient p k b n

/-- Full part (i), including the integer/noninteger case split. -/
theorem minor_parameters (a : ℚ) (ha : 1 ≤ a) :
    ∃ A : Algorithm, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G (a:ℝ) → (∀ v, (G.neighborFinset v).Nonempty) →
      ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G A a codec := by
  classical
  by_cases hz : ∃ z : ℤ, (z:ℚ) = 2*a
  · obtain ⟨z,hz⟩ := hz
    have hz2 : (2:ℤ) ≤ z := by
      have hh : (2:ℚ) ≤ (z:ℚ) := by linarith
      exact_mod_cast hh
    let d := z.toNat
    have hd : 2 ≤ d := by omega
    have hdQ : (d:ℚ) = 2*a := by
      have he : (d:ℤ) = z := Int.toNat_of_nonneg (by omega)
      have heQ : (d:ℚ) = (z:ℚ) := by exact_mod_cast he
      exact heQ.trans hz
    have hdR : (d:ℝ)/2 = (a:ℝ) := by
      have hh : (d:ℝ) = 2*(a:ℝ) := by exact_mod_cast hdQ
      linarith
    obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := IntegerSolver.parameters d hd
    refine ⟨integerAlgorithm (by omega : 1 ≤ d) p t k b n,?_⟩
    intro V _ _ G _ hden hfree ids codec
    have hm : MinorDensity.Bound G ((d:ℝ)/2) := by rwa [hdR]
    have hs := hp G hm hfree codec
    refine ⟨hs.1,?_,?_,IntegerSolver.logarithmic_bits codec p t k b n (by omega) (Fintype.card V)⟩
    · have hh := hs.2
      change ((IntegerSolver.output G codec p t k b n (by omega)).card : ℝ) ≤
        2*(a:ℝ)*FractionalSolver.fractionalNumber G
      change ((IntegerSolver.output G codec p t k b n (by omega)).card : ℝ) ≤
        (d:ℝ)*FractionalSolver.fractionalNumber G at hh
      have he : (d:ℝ) = 2*(a:ℝ) := by linarith
      have heprod := congrArg (fun r : ℝ => r*FractionalSolver.fractionalNumber G) he
      linarith
    · change (IntegerSolver.runtime codec p t k b n (by omega)).rounds = _
      rw [IntegerSolver.rounds,GeneralCoveringFractionalEndpoint.rounds]
      rfl
  · obtain ⟨A,hA⟩ := subgraph_parameters a a ha le_rfl hz
    refine ⟨A,?_⟩
    intro V _ _ G _ hden hfree ids codec
    exact hA G hden hfree (MinorDensity.induced_bound G hden) codec

end Paper.TotalDomination.ExactEndpoint
#print axioms Paper.TotalDomination.ExactEndpoint.minor_parameters
#print axioms Paper.TotalDomination.ExactEndpoint.subgraph_parameters
