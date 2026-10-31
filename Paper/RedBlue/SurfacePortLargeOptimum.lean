import Paper.RedBlue.SurfacePort
/-! The large-optimum consequence of `fv:rb:surface`, with the same actual
port-broadcast program and the same uniform parameters as the additive bound.
The signed-rotation input remains explicit; the ordinary surface bridge is separate.
-/
namespace Paper.RedBlue
open BroadcastModel
theorem large_optimum_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (ε/4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ g) →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G)
        (R B : Finset V), Disjoint R B → ∀ c : V → Fin (M+1),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      (M : ℝ)*g/ε ≤ GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ)) →
      let D := Finset.univ.filter (fun v => (surfacePortProgram I p t k b n hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4+2*ε)*GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ)) := by
  obtain ⟨p,t,k,b,n,ht,hk,hs⟩ := surface_port_parameters g M hM ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hgen ids I ports R B hRB c hne hc hlarge
  have h := hs G hgen I ports R B hRB c hne hc
  dsimp only at h ⊢
  refine ⟨h.1,h.2.1,?_⟩
  have hbudget := (div_le_iff₀ hε).mp hlarge
  nlinarith [h.2.2]
end Paper.RedBlue
#print axioms Paper.RedBlue.large_optimum_parameters
