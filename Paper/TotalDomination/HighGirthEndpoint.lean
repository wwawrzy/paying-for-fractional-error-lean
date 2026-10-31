import Paper.TotalDomination.HighGirthSolver
import Paper.Preliminaries.PlanarDensity
import Paper.Endpoints.Girth.CurrentPlanarFaceBound

namespace Paper.TotalDomination.HighGirthEndpoint
open BroadcastModel
structure Config (rho a : ℝ) where
  p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 (HighGirthSlackArithmetic.accuracy a)
  t : ℕ
  k : ℕ
  b : ℕ
  n : ℕ
  ht : 0 < t
  hk : 0 < k
noncomputable def runtime {rho a : ℝ} (C : Config rho a) {V : Type} [LinearOrder V]
    {ids : ℕ} (codec : BitCode V ids) : Program V PUnit Bool :=
  HighGirthSolver.runtime codec C.p C.t C.k C.b C.n (by norm_num)
noncomputable def roundBound {rho a : ℝ} (C : Config rho a) : ℕ :=
  GeneralCoveringInitializerFractional.scale rho*(5+2*GeneralCoveringInitializerFractional.listThreshold rho)+
    18+4*GeneralCoveringOwnerFrameTaskInputs.outerRadius C.k C.n+
    RecursiveSearch.roundBound (4*C.k) C.p.A (GeneralCoveringTaskFractionalSolve.numeratorBound C.p.A 2 C.k C.p.q)+9
noncomputable def bitsCoefficient {rho a : ℝ} (C : Config rho a) (c : ℕ) : ℕ :=
  HighGirthSolver.coefficient C.p C.k C.b C.n c
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def output {rho a : ℝ} (C : Config rho a) {ids : ℕ} (codec : BitCode V ids) : Finset V :=
  HighGirthSolver.output G codec C.p C.t C.k C.b C.n (by norm_num)
def Outcome {rho a : ℝ} (C : Config rho a) {ids : ℕ} (codec : BitCode V ids) : Prop :=
  (∀ r, ∃ v ∈ output G C codec, G.Adj r v) ∧
  ((output G C codec).card : ℝ) ≤ 2*HighGirthSelection.totalFractionalNumber G ∧
  (runtime C codec).rounds=roundBound C ∧
  ∀ c, ids ≤ c*Nat.clog 2 (Fintype.card V+2) →
    (runtime C codec).maxBits ≤ bitsCoefficient C c*Nat.clog 2 (Fintype.card V+2)

theorem parameters (rho a : ℝ) (hrho : 1 ≤ rho) (ha : 1 ≤ a) (hhi : a < 9/8) :
    ∃ C : Config rho a, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
      Incidence.InducedDensityBound G a → ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G C codec := by
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := HighGirthSolver.parameters rho a hrho ha hhi
  let C : Config rho a := ⟨p,t,k,b,n,ht,hk⟩
  refine ⟨C,?_⟩
  intro V _ _ G _ hm hf hd ids codec
  have h := hp G hm hf hd codec
  refine ⟨h.1,h.2,?_,?_⟩
  · change (HighGirthSolver.runtime codec p t k b n (by norm_num)).rounds=_
    rw [HighGirthSolver.rounds,GeneralCoveringFractionalEndpoint.rounds]
    rfl
  · exact HighGirthSolver.logarithmic_bits codec p t k b n (by norm_num) (Fintype.card V)

/-- Actual graph-uniform broadcast algorithm, including fixed round and
logarithmic message bounds, on every isolate-free planar graph of girth>=19. -/
theorem planar_parameters :
    ∃ C : Config 3 (19/17), ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsPlanar → (∀ v, (G.neighborFinset v).Nonempty) →
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → 19 ≤ p.length) →
      ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G C codec := by
  obtain ⟨C,hC⟩ := parameters 3 (19/17) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,?_⟩
  intro V _ _ G _ hp hf hg ids codec
  have hd := CurrentPlanarFaceBound.induced_density hp 19 (by norm_num) hg
  norm_num at hd
  exact hC G (PlanarDensity.minor_density G hp) hf hd codec

end Paper.TotalDomination.HighGirthEndpoint
#print axioms Paper.TotalDomination.HighGirthEndpoint.planar_parameters
