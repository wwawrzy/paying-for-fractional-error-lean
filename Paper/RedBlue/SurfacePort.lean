import Paper.RedBlue.SurfaceResources
import Paper.RedBlue.LocalPreparation
namespace Paper.RedBlue
open BroadcastModel
variable {V : Type} [LinearOrder V]
noncomputable def surfacePortProgram {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) : PortBroadcastModel.Program V (LocalInput M) Bool :=
  KT0Compiler.program I (.seq (localPreparation M)
    (.seq (surfaceIntegralProgram I p t k b n hM) (.local fun _ _ o => o.selected)))
variable [Fintype V]
theorem surface_port_correct (G : SimpleGraph V) [DecidableRel G.Adj] {ids M g : ℕ}
    (I : BitCode V ids) {ε : ℝ} (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (ports : PortBroadcastModel.Numbering G)
    (R B : Finset V) (c : V → Fin (M+1)) :
    (surfacePortProgram I p t k b n hM).runEncoded G ports (localInput R B c) =
      fun v => ((surfaceIntegralProgram I p t k b n hM).runEncoded G (solverInput G R B c) v).selected := by
  rw [surfacePortProgram,KT0Compiler.program_encoded_correct]
  simp only [Program.runEncoded_eq_run,Program.run,localPreparation_correct]
theorem surface_port_rounds {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :
    (surfacePortProgram I p t k b n hM).rounds =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).rounds+5 := by
  simp only [surfacePortProgram,KT0Compiler.program_rounds,Program.rounds,
    localPreparation_rounds,surface_integral_rounds]
  omega
theorem surface_port_bits {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (N c : ℕ) (hids : ids ≤ c*Nat.clog 2 (N+2)) :
    (surfacePortProgram I p t k b n hM).maxBits ≤
      max c (max 2 (GeneralCoveringFrameAverageResources.coefficient
        (GeneralCoveringInitializerFractional.listThreshold (3*(g : ℝ)+3))
        p.L p.Δ p.A M k b n p.q c+M+c+3))*Nat.clog 2 (N+2) := by
  apply KT0Compiler.logarithmic_bits I _ N c _ hids
  simp only [Program.maxBits,localPreparation_bits,Nat.max_zero]
  have hs := surface_integral_logarithmic_bits I p t k b n hM N c hids
  have hl : 1 ≤ Nat.clog 2 (N+2) := Nat.clog_pos (by omega) (by omega)
  exact (max_le_max (by nlinarith : 2 ≤ 2*Nat.clog 2 (N+2)) hs).trans_eq (by rw [max_mul_mul_right])
theorem surface_port_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (ε/4),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ g) →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G)
        (R B : Finset V), Disjoint R B → ∀ c : V → Fin (M+1),
        (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      let D := Finset.univ.filter (fun v => (surfacePortProgram I p t k b n hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      (∑ v ∈ D, ((c v).val : ℝ)) ≤ (4+ε)*GeneralCoveringNormalizedFractional.supportedNumber
        (rows G R B) R (fun v => ((c v).val : ℝ))+(M : ℝ)*g := by
  obtain ⟨p,t,k,b,n,ht,hk,hs⟩ := surface_integral_parameters g M hM ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hgen ids I ports R B hRB c hne hc
  dsimp only
  rw [surface_port_correct]
  exact hs G hgen I R B hRB c hne hc
end Paper.RedBlue
#print axioms Paper.RedBlue.surface_port_correct
#print axioms Paper.RedBlue.surface_port_rounds
#print axioms Paper.RedBlue.surface_port_bits
#print axioms Paper.RedBlue.surface_port_parameters
