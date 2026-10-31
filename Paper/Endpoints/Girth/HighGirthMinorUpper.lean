import Paper.Endpoints.Girth.HighGirthPlanar17Program
import Paper.Endpoints.Girth.HighGirthMinorParameters
import Paper.Endpoints.Girth.HighGirthDilution

/-! The actual uniform KT0 broadcast CONGEST upper branch of fv:hg:minor-three,
with its exact rational floor/max girth threshold. The separate proper-class
and lower-bound statements are not claimed by this module. -/
namespace Paper.HighGirthMinorUpper
open HighGirthPlanar17Program

theorem uniform_input (rho : Rat) (hrho : 1 ≤ rho) :
    ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (rho : Real) → ∀ {b : Nat} (C : BroadcastModel.BitCode V b),
        SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) (fractional G C p) ∧
        (∀ v ∈ HighGirthTransformation.zone G, fractional G C p v ≤ 1) ∧
        SevenFoundation.cost (HighGirthAuxiliary.auxiliary G) (fractional G C p) ≤
          (1+(HighGirthSlackParameter.delta (HighGirthMinorParameters.density rho):Real))*HighGirthAuxiliary.number G := by
  classical
  have hrhoR : (1:Real) ≤ (rho:Real) := by exact_mod_cast hrho
  have hdelta : (0:Real) < (HighGirthSlackParameter.delta (HighGirthMinorParameters.density rho):Real) :=
    Rat.cast_pos.mpr (HighGirthMinorParameters.accuracy_pos rho hrho)
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hp⟩ := GeneralFractionalBroadcast.parameters
    (rho:Real) hrhoR 3 _ hdelta
  let p : Config := ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq⟩
  refine ⟨p,?_⟩
  intro V _ _ G _ hm b C
  have h := hp (HighGirthMaskedInput.graph G) (MaskedTaskGraph.density G _ hm) C
    (HighGirthTransformation.demands G) (HighGirthMaskedInput.weight G) (HighGirthMaskedInput.weight_pos G)
  exact HighGirthNearOptimalInput.transfer G _ _ h.1 h.2

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

theorem upper (rho : Rat) (hrho : 1 ≤ rho) :
    ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (rho:Real) →
        (∀ (v : V) (w : G.Walk v v), w.IsCycle → HighGirthMinorParameters.girth rho ≤ w.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : Nat} (C : BroadcastModel.BitCode V b),
        SevenFoundation.dominates G (output G ports C p) ∧
        ((output G ports C p).card:Real) ≤ 3*SevenFoundation.fractionalNumber G ∧
        (program C p).rounds = roundBound p ∧
        ∀ n c : Nat, b ≤ c*Nat.clog 2 (n+2) →
          (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n+2) := by
  obtain ⟨p,hp⟩ := uniform_input rho hrho
  refine ⟨p,?_⟩
  intro V _ _ G _ hm hg ports b C
  have h := hp G hm C
  obtain ⟨_,_,_,hdom,hcard⟩ := HighGirthStaticThree.coefficient_three_static
    G (fractional G C p) (HighGirthMinorParameters.density rho)
    (HighGirthMinorParameters.density_range rho hrho).1
    (HighGirthMinorParameters.density_range rho hrho).2 h.1 h.2.1
    (diluted_density rho hrho G hm hg) h.2.2
  refine ⟨?_,?_,rounds C p,fun n c hids => logarithmic_bits C p n c hids⟩
  · rw [output_eq]
    exact hdom
  · rw [output_eq]
    exact hcard

end Paper.HighGirthMinorUpper
#print axioms Paper.HighGirthMinorUpper.uniform_input
#print axioms Paper.HighGirthMinorUpper.diluted_density
#print axioms Paper.HighGirthMinorUpper.upper
