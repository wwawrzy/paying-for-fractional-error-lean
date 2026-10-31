import Paper.TotalDomination.IntegerDefectSolver
import Paper.TotalDomination.ExactEndpoint
import Paper.Endpoints.Girth.NoncriticalGirth

/-! Actual exact upper bounds for every planar girth, including g=3,4,6.
Optimality and the improved gain table are separate assertions. -/
namespace Paper.TotalDomination.PlanarGirthEndpoint
open BroadcastModel ExactEndpoint

noncomputable def roundBound {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (k n : ℕ) : ℕ :=
  GeneralCoveringInitializerFractional.scale rho*(5+2*GeneralCoveringInitializerFractional.listThreshold rho)+
    18+4*GeneralCoveringOwnerFrameTaskInputs.outerRadius k n+
    RecursiveSearch.roundBound (4*k) p.A (GeneralCoveringTaskFractionalSolve.numeratorBound p.A d k p.q)+9

noncomputable def algorithm {rho ε : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) : Algorithm where
  runtime := fun codec => IntegerSolver.runtime codec p t k b n hd
  roundBound := roundBound p k n
  bitsCoefficient := IntegerSolver.coefficient p k b n

theorem integer_parameters (g d : ℕ) (hg : 3 ≤ g) (hd : 2 ≤ d)
    (hdg : (d:ℝ) = 2*((g:ℝ)/((g:ℝ)-2))) :
    ∃ A : Algorithm, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsPlanar → (∀ v, (G.neighborFinset v).Nonempty) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G A ((d:ℚ)/2) codec := by
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := IntegerDefectSolver.planar_parameters g d hg hd hdg
  refine ⟨algorithm (by omega : 1 ≤ d) p t k b n,?_⟩
  intro V _ _ G _ hplanar hfree hgirth ids codec
  have hs := hp G hplanar hfree hgirth codec
  refine ⟨hs.1,?_,?_,IntegerSolver.logarithmic_bits codec p t k b n (by omega) (Fintype.card V)⟩
  · have hh := hs.2
    change ((IntegerSolver.output G codec p t k b n (by omega)).card:ℝ) ≤
      2*((((d:ℚ)/2):ℚ):ℝ)*FractionalSolver.fractionalNumber G
    have he : 2*((((d:ℚ)/2):ℚ):ℝ) = (d:ℝ) := by push_cast;ring
    rw [he]
    exact hh
  · change (IntegerSolver.runtime codec p t k b n (by omega)).rounds = _
    rw [IntegerSolver.rounds,GeneralCoveringFractionalEndpoint.rounds]
    rfl

/-- For every g>=3, the actual graph-uniform constant-round algorithm
achieves 2g/(g-2) against the fractional total domination benchmark. -/
theorem parameters (g : ℕ) (hg : 3 ≤ g) :
    ∃ A : Algorithm, ∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsPlanar → (∀ v, (G.neighborFinset v).Nonempty) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {ids : ℕ} (codec : BitCode V ids), Outcome G A (NoncriticalGirth.density g) codec := by
  by_cases h3 : g = 3
  · subst g
    convert integer_parameters 3 6 (by decide) (by decide) (by norm_num) using 1 <;>
      norm_num [NoncriticalGirth.density]
  by_cases h4 : g = 4
  · subst g
    convert integer_parameters 4 4 (by decide) (by decide) (by norm_num) using 1 <;>
      norm_num [NoncriticalGirth.density]
  by_cases h6 : g = 6
  · subst g
    convert integer_parameters 6 3 (by decide) (by decide) (by norm_num) using 1 <;>
      norm_num [NoncriticalGirth.density]
  have hg5 : 5 ≤ g := by omega
  obtain ⟨A,hA⟩ := ExactEndpoint.subgraph_parameters 3 (NoncriticalGirth.density g)
    (NoncriticalGirth.density_bounds g hg).1 (NoncriticalGirth.density_bounds g hg).2
    (NoncriticalGirth.density_noninteger g hg5 h6)
  refine ⟨A,?_⟩
  intro V _ _ G _ hplanar hfree hgirth ids codec
  have hden := CurrentPlanarFaceBound.induced_density hplanar g hg hgirth
  rw [← NoncriticalGirth.density_cast] at hden
  exact hA G (PlanarDensity.minor_density G hplanar) hfree hden codec

end Paper.TotalDomination.PlanarGirthEndpoint
#print axioms Paper.TotalDomination.PlanarGirthEndpoint.parameters
