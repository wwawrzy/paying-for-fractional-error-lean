import Paper.TotalDomination.PlanarGainArithmetic
import Paper.TotalDomination.NonintegerEndpoint

/-! The improved noninteger rows of the planar total-domination table,
with the actual solver, capping, rounding and physical resource guarantees. -/
namespace Paper.TotalDomination.PlanarGainEndpoint
open BroadcastModel NoncriticalGirth

 def Specification (g : ℕ) (C : NonintegerEndpoint.Config 3 (density g)) (factor : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsPlanar → (∀ v, (G.neighborFinset v).Nonempty) →
    (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
    ∀ {ids : ℕ} (codec : BitCode V ids),
      (∀ r, ∃ v ∈ NonintegerEndpoint.output G C codec, G.Adj r v) ∧
      ((NonintegerEndpoint.output G C codec).card:ℝ) ≤ factor*FractionalSolver.fractionalNumber G ∧
      (NonintegerEndpoint.runtime C codec).rounds = NonintegerEndpoint.roundBound C ∧
      ∀ c, ids ≤ c*Nat.clog 2 (Fintype.card V+2) →
        (NonintegerEndpoint.runtime C codec).maxBits ≤
          NonintegerEndpoint.bitsCoefficient C c*Nat.clog 2 (Fintype.card V+2)

theorem of_specification (g : ℕ) (hg : 3 ≤ g) (C : NonintegerEndpoint.Config 3 (density g))
    (factor : ℝ) (hC : NonintegerEndpoint.Specification C factor) : Specification g C factor := by
  intro V _ _ G _ hplanar hfree hgirth ids codec
  have hden := CurrentPlanarFaceBound.induced_density hplanar g hg hgirth
  rw [← density_cast] at hden
  exact hC G (PlanarDensity.minor_density G hplanar) hfree hden codec

/-- Exact rational coefficients for g=7,...,13, with no solver error left. -/
theorem finite_parameters (g : ℕ) (hg : 7 ≤ g) (hhi : g ≤ 13) :
    ∃ C : NonintegerEndpoint.Config 3 (density g),
      Specification g C (PlanarGainArithmetic.coefficient g:ℝ) := by
  obtain ⟨hpos,hbelow,hcoef⟩ := PlanarGainArithmetic.finite_targets g hg hhi
  obtain ⟨C,hC⟩ := NonintegerEndpoint.parameters_below_max 3 (by norm_num) (density g)
    (density_bounds g (by omega)).1 (density_noninteger g (by omega) (by omega))
    (PlanarGainArithmetic.target g:ℝ) hpos hbelow
  have he : 2*(density g:ℝ)-(PlanarGainArithmetic.target g:ℝ) =
      (PlanarGainArithmetic.coefficient g:ℝ) := by exact_mod_cast hcoef
  rw [he] at hC
  exact ⟨C,of_specification g (by omega) C _ hC⟩

/-- The g=5 row for every positive real epsilon, with public rational
solver/gain parameters selected before the graph. -/
theorem five_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ C : NonintegerEndpoint.Config 3 (density 5), Specification 5 C (3+ε) := by
  obtain ⟨C,hC⟩ := NonintegerEndpoint.parameters_near_max 3 (by norm_num) (density 5)
    (density_bounds 5 (by decide)).1 (density_noninteger 5 (by decide) (by decide)) ε hε
  rw [PlanarGainArithmetic.five_max] at hC
  exact ⟨C,of_specification 5 (by decide) C _ hC⟩

/-- Every g>=14 has coefficient2+epsilon. The exact2 g>=19 result is
separate and is not claimed by this approximation theorem. -/
theorem large_parameters (g : ℕ) (hg : 14 ≤ g) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : NonintegerEndpoint.Config 3 (density g), Specification g C (2+ε) := by
  obtain ⟨C,hC⟩ := NonintegerEndpoint.parameters_near_max 3 (by norm_num) (density g)
    (density_bounds g (by omega)).1 (density_noninteger g (by omega) (by omega)) ε hε
  rw [PlanarGainArithmetic.large_max g hg] at hC
  exact ⟨C,of_specification g (by omega) C _ hC⟩

end Paper.TotalDomination.PlanarGainEndpoint
#print axioms Paper.TotalDomination.PlanarGainEndpoint.finite_parameters
#print axioms Paper.TotalDomination.PlanarGainEndpoint.large_parameters
