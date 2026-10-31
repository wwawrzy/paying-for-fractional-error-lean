import Paper.Endpoints.Rounding.ImprovedExcessSolver
namespace Paper.ImprovedExcessSolver
open BroadcastModel SevenFoundation
set_option maxHeartbeats 1000000 in
theorem fixed_gain_parameters (rho : ℝ) (hrho : 1 ≤ rho) (a μ : ℚ) (η δ : ℝ)
    (ha : 1 ≤ a) (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2*a)
    (hμ : 0 ≤ μ) (hμθ : (μ : ℝ) ≤ ImprovedExcessEndpoint.gap a)
    (hadm : ((μ : ℝ)+1)*((μ : ℝ)+1-ImprovedExcessEndpoint.gap a) ≤
      (2*(a : ℝ)+1)*(1-ImprovedExcessEndpoint.gap a)/(a : ℝ))
    (hη : 0 ≤ η) (hδ : 0 < δ) :
    ∃ p : Config a, p.mu = μ ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G rho → ImprovedExcess.DensityWithExcess G (a : ℝ) η →
      ∀ {b : ℕ} (C : BitCode V b), dominates G (output G C p) ∧
        ((output G C p).card : ℝ) ≤
          (2*(a : ℝ)+1-(μ : ℝ))*(1+δ)*fractionalNumber G+
            ImprovedExcess.additive (a : ℝ) (ImprovedExcessEndpoint.gap a) (μ : ℝ) η := by
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hs⟩ := CappedWholeProgram.parameters rho hrho δ hδ
  let p : Config a := ⟨μ,A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq⟩
  refine ⟨p,rfl,?_⟩
  intro V _ _ G _ hminor hden b C
  obtain ⟨hy,hcap,hmass⟩ := hs G hminor C
  have ht := ImprovedExcessEndpoint.rounding G a μ η ha hnoninteger hμ hμθ hη hadm hden
    (solution G C p) hy hcap
  obtain ⟨hθ,hθ1⟩ := ImprovedExcessEndpoint.gap_bounds a ha hnoninteger
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb : 0 ≤ 2*(a : ℝ)+1-(μ : ℝ) := by linarith
  rw [output_eq]
  refine ⟨ht.1,ht.2.1.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hmass hb
  change (2*(a : ℝ)+1-(μ : ℝ))*(∑ v, solution G C p v)+
    ImprovedExcess.additive (a : ℝ) (ImprovedExcessEndpoint.gap a) (μ : ℝ) η ≤ _
  calc
    _ ≤ (2*(a : ℝ)+1-(μ : ℝ))*((1+δ)*fractionalNumber G)+
        ImprovedExcess.additive (a : ℝ) (ImprovedExcessEndpoint.gap a) (μ : ℝ) η := add_le_add hh le_rfl
    _ = _ := by ring
end Paper.ImprovedExcessSolver
#print axioms Paper.ImprovedExcessSolver.fixed_gain_parameters
