import Paper.TotalDomination.HighGirthEndpoint
import Paper.TotalDomination.HighGirthMinorParameters
import Paper.Endpoints.Girth.HighGirthDilution
namespace Paper.TotalDomination.HighGirthMinorEndpoint
set_option backward.isDefEq.respectTransparency false in
theorem diluted_density (rho : Rat) (hrho : 1 ≤ rho)
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinorDensity.Bound G (rho:Real))
    (hg : ∀ (v : V) (w : G.Walk v v), w.IsCycle → HighGirthMinorParameters.girth rho ≤ w.length) :
    Incidence.InducedDensityBound G (HighGirthMinorParameters.density rho:Real) := by
  classical
  intro S
  have hg' : ∀ (v : V) (w : G.Walk v v), w.IsCycle → 8*HighGirthMinorParameters.radius rho+2 < w.length := by
    intro v w hw
    exact lt_of_lt_of_le (HighGirthMinorParameters.girth_strict rho) (hg v w hw)
  have hrhoR : (1:Real) ≤ (rho:Real) := by exact_mod_cast hrho
  have h := HighGirthDilution.density (G.induce (S:Set V)) (rho:Real) hrhoR
    (HighGirthMinorParameters.radius rho) (HighGirthMinorParameters.radius_pos rho)
    (HighGirthDilution.minor_induce G _ hm _) (HighGirthDilution.girth_induce G _ hg' _)
  simpa only [SimpleGraph.inducedEdgeCount,SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card,
    Finset.coe_sort_coe,Nat.card_eq_finsetCard,HighGirthMinorParameters.density,
    Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_sub,Rat.cast_natCast] using h

theorem parameters (rho : ℚ) (hrho : 1 ≤ rho) :
    ∃ C : HighGirthEndpoint.Config (rho:ℝ) (HighGirthMinorParameters.density rho:ℝ),
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (rho:ℝ) → (∀ v, (G.neighborFinset v).Nonempty) →
        (∀ (v : V) (p : G.Walk v v), p.IsCycle → HighGirthMinorParameters.girth rho ≤ p.length) →
        ∀ {ids : ℕ} (codec : BroadcastModel.BitCode V ids), HighGirthEndpoint.Outcome G C codec := by
  have hrhoR : (1:ℝ) ≤ (rho:ℝ) := by exact_mod_cast hrho
  have hA := HighGirthMinorParameters.density_range rho hrho
  have ha : (1:ℝ) ≤ (HighGirthMinorParameters.density rho:ℝ) := by exact_mod_cast hA.1
  have hhi : (HighGirthMinorParameters.density rho:ℝ) < ((9/8:ℚ):ℝ) := Rat.cast_lt.mpr hA.2
  norm_num at hhi
  obtain ⟨C,hC⟩ := HighGirthEndpoint.parameters (rho:ℝ) (HighGirthMinorParameters.density rho:ℝ) hrhoR ha hhi
  refine ⟨C,?_⟩
  intro V _ _ G _ hm hf hg ids codec
  exact hC G hm hf (diluted_density rho hrho G hm hg) codec
end Paper.TotalDomination.HighGirthMinorEndpoint
#print axioms Paper.TotalDomination.HighGirthMinorEndpoint.parameters
