import GraphTheory.Surfaces.OrdinarySurface
import Paper.RedBlue.SurfacePortLargeOptimum
import Paper.RedBlue.AbsorbedPort
namespace Paper.RedBlueOrdinarySurface
open BroadcastModel RedBlue
theorem additive_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (ε/4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G g →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G)
        (R B : Finset V), Disjoint R B → ∀ c : V → Fin (M+1),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      let D := Finset.univ.filter (fun v => (surfacePortProgram I p t k b n hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4+ε)*GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ))+(M : ℝ)*g := by
  obtain ⟨p,t,k,b,n,ht,hk,hs⟩ := RedBlue.surface_port_parameters g M hM ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hsurface
  exact hs G (SimpleGraph.OrdinarySurface.signedRotation_real G g hsurface)

theorem large_optimum_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (ε/4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G g →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G)
        (R B : Finset V), Disjoint R B → ∀ c : V → Fin (M+1),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      (M : ℝ)*g/ε ≤ GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ)) →
      let D := Finset.univ.filter (fun v => (surfacePortProgram I p t k b n hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4+2*ε)*GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ)) := by
  obtain ⟨p,t,k,b,n,ht,hk,hs⟩ := RedBlue.large_optimum_parameters g M hM ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hsurface
  exact hs G (SimpleGraph.OrdinarySurface.signedRotation_real G g hsurface)

theorem absorbed_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℚ, ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (4*(δ : ℝ)/4),
      ∃ t k b n K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G g →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G) (R B : Finset V),
      Disjoint R B → ∀ c : V → Fin (M+1),
      (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      let D := Finset.univ.filter (fun v => (RedBlueSurfaceAbsorption.portProgram I p t k b n (3*g+3) K hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      ((∑ v ∈ D, (c v).val : ℕ) : ℝ) ≤ (4+ε)*(IntegralCoverOptimum.optimum (rows G R B) R (fun v => (c v).val) : ℝ) := by
  obtain ⟨δ,p,t,k,b,n,K,hs⟩ := RedBlueSurfaceAbsorption.port_parameters g M hM ε hε
  refine ⟨δ,p,t,k,b,n,K,?_⟩
  intro V _ _ G _ hsurface
  exact hs G (SimpleGraph.OrdinarySurface.signedRotation_real G g hsurface)

end Paper.RedBlueOrdinarySurface
#print axioms Paper.RedBlueOrdinarySurface.additive_parameters
#print axioms Paper.RedBlueOrdinarySurface.large_optimum_parameters
#print axioms Paper.RedBlueOrdinarySurface.absorbed_parameters
