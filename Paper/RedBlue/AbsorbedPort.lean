import Paper.RedBlue.SurfaceAbsorption
import Paper.RedBlue.LocalPreparation
import Paper.RedBlue.SurfaceResources
import Paper.Endpoints.Rounding.AbsorptionPortResources
namespace Paper.RedBlueSurfaceAbsorption
open BroadcastModel RedBlue
variable {V : Type} [LinearOrder V]
def prepare {M : ℕ} : Program V (LocalInput M) (GeneralCoveringFractional.Input V M) :=
  .seq (localPreparation M) (.local fun _ _ s => ⟨true,s.2,s.1.residual,s.1.candidates,s.1.targets⟩)
noncomputable def prepared {M : ℕ} (A : Program V (GeneralCoveringFractional.Input V M) Bool) : Program V (LocalInput M) Bool :=
  .seq (.local fun _ _ s => (s,s.blue))
    (.seq (ProgramMemory.carry (.seq prepare A)) (.local fun _ _ s => s.1 && s.2))
noncomputable def portProgram {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n a K : ℕ) (hM : 1 ≤ M) : PortBroadcastModel.Program V (LocalInput M) Bool :=
  KT0Compiler.program I (prepared (program I p t k b n a K hM))
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem prepare_correct {M : ℕ} (R B : Finset V) (c : V → Fin (M+1)) :
    prepare.run G (localInput R B c) = input G R B c := by
  change (fun v => let s := (localPreparation M).run G (localInput R B c) v;
    (⟨true,s.2,s.1.residual,s.1.candidates,s.1.targets⟩ : GeneralCoveringFractional.Input V M)) = _
  rw [localPreparation_correct]
  rfl
theorem port_output {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n a K : ℕ) (hM : 1 ≤ M) (ports : PortBroadcastModel.Numbering G)
    (R B : Finset V) (c : V → Fin (M+1)) :
    Finset.univ.filter (fun v => (portProgram I p t k b n a K hM).runEncoded G ports (localInput R B c) v = true) =
      (Finset.univ.filter (fun v => (program I p t k b n a K hM).runEncoded G (input G R B c) v = true)) ∩ B := by
  classical
  rw [portProgram,KT0Compiler.program_encoded_correct]
  simp only [prepared,Program.runEncoded_eq_run,Program.run]
  rw [ProgramMemory.run]
  change Finset.univ.filter (fun v => ((program I p t k b n a K hM).run G
      (prepare.run G (localInput R B c)) v && (localInput R B c v).blue) = true) = _
  rw [prepare_correct]
  ext v
  simp [localInput,Program.runEncoded_eq_run]
theorem port_rounds {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n a K : ℕ) (hM : 1 ≤ M) :
    (portProgram I p t k b n a K hM).rounds =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).rounds+5+SmallComponentProgram.roundBound a K := by
  simp only [portProgram,KT0Compiler.program_rounds,prepared,Program.rounds,ProgramMemory.rounds,
    prepare,localPreparation_rounds,program,ComponentReplacementProgram.rounds,base,
    toSolver,surface_integral_rounds,SmallComponentProgram.rounds]
  omega
theorem port_bits {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n a K : ℕ) (hM : 1 ≤ M) (N c : ℕ) (hids : ids ≤ c*Nat.clog 2 (N+2)) :
    (portProgram I p t k b n a K hM).maxBits ≤
      max c (max 2 (max (GeneralCoveringFrameAverageResources.coefficient
        (GeneralCoveringInitializerFractional.listThreshold (3*(g : ℝ)+3))
        p.L p.Δ p.A M k b n p.q c+M+c+3)
        (SmallComponentProgram.messageConstant a M K c)))*Nat.clog 2 (N+2) := by
  apply KT0Compiler.logarithmic_bits I _ N c _ hids
  simp only [prepared,Program.maxBits,ProgramMemory.maxBits,prepare,localPreparation_bits,
    program,ComponentReplacementProgram.maxBits,base,toSolver,Nat.zero_max,Nat.max_zero]
  have hs := surface_integral_logarithmic_bits I p t k b n hM N c hids
  have hm := SmallComponentProgram.logarithmic_bits I a M K hM N c hids
  have hl : 1 ≤ Nat.clog 2 (N+2) := Nat.clog_pos (by omega) (by omega)
  exact (max_le_max (by nlinarith : 2 ≤ 2*Nat.clog 2 (N+2))
    ((max_le_max hs hm).trans_eq (by rw [max_mul_mul_right]))).trans_eq (by rw [max_mul_mul_right])
set_option maxHeartbeats 800000 in
theorem port_parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℚ, ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (4*(δ : ℝ)/4),
      ∃ t k b n K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ g) →
      ∀ {ids : ℕ} (I : BitCode V ids) (ports : PortBroadcastModel.Numbering G) (R B : Finset V),
      Disjoint R B → ∀ c : V → Fin (M+1),
      (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      let D := Finset.univ.filter (fun v => (portProgram I p t k b n (3*g+3) K hM).runEncoded G ports (localInput R B c) v = true)
      D ⊆ B ∧ (∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v) ∧
      ((∑ v ∈ D, (c v).val : ℕ) : ℝ) ≤ (4+ε)*(IntegralCoverOptimum.optimum (rows G R B) R (fun v => (c v).val) : ℝ) := by
  obtain ⟨δ,p,t,k,b,n,K,hs⟩ := parameters g M hM ε hε
  refine ⟨δ,p,t,k,b,n,K,?_⟩
  intro V _ _ G _ hrot ids I ports R B hRB c hrows hc
  have hb := hs G hrot I R B hRB c hrows hc
  dsimp only
  rw [port_output]
  refine ⟨Finset.inter_subset_right,?_,?_⟩
  · intro r hr
    obtain ⟨v,hv,hrow⟩ := hb.1 r hr
    obtain ⟨_,hadj,hblue⟩ := (mem_rows G R B r v).mp hrow
    exact ⟨v,Finset.mem_inter.mpr ⟨hv,hblue⟩,hblue,hadj⟩
  · have hh : (∑ v ∈ (Finset.univ.filter (fun v => (program I p t k b n (3*g+3) K hM).runEncoded G (input G R B c) v = true)) ∩ B, (c v).val) ≤
        ∑ v ∈ Finset.univ.filter (fun v => (program I p t k b n (3*g+3) K hM).runEncoded G (input G R B c) v = true), (c v).val :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_left
    apply le_trans ?_ hb.2
    exact_mod_cast hh
end Paper.RedBlueSurfaceAbsorption
#print axioms Paper.RedBlueSurfaceAbsorption.port_output
#print axioms Paper.RedBlueSurfaceAbsorption.port_rounds
#print axioms Paper.RedBlueSurfaceAbsorption.port_bits
#print axioms Paper.RedBlueSurfaceAbsorption.port_parameters
