import Paper.RedBlue.SurfaceIntegral
import Paper.Endpoints.Rounding.AbsorptionRuntimeBound
import Paper.Endpoints.Rounding.AbsorptionPublicParameters
import Paper.Endpoints.Components.ComponentDensity
import Paper.Endpoints.Rounding.SurfaceRotationDensityClass
namespace Paper.RedBlueSurfaceAbsorption
open BroadcastModel RedBlue
variable {V : Type} [LinearOrder V]
def toSolver {M : ℕ} : Program V (GeneralCoveringFractional.Input V M) (GeneralCoveringFractionalEndpoint.Input V M) :=
  .local fun _ _ s => (⟨s.demand,s.candidates,s.targets⟩,s.cost)
noncomputable def base {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) : Program V (GeneralCoveringFractional.Input V M) Bool :=
  .seq toSolver (.seq (surfaceIntegralProgram I p t k b n hM) (.local fun _ _ o => o.selected))
noncomputable def program {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n a K : ℕ) (hM : 1 ≤ M) :=
  ComponentReplacementProgram.program (base I p t k b n hM) (SmallComponentProgram.program I a M K hM)
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def input {M : ℕ} (R B : Finset V) (c : V → Fin (M+1)) (v : V) : GeneralCoveringFractional.Input V M := by
  classical
  exact ⟨true,c v,decide (v ∈ R),rows G R B v,targets G R B v⟩
theorem base_correct {ids M g : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (R B : Finset V) (c : V → Fin (M+1)) :
    Finset.univ.filter (fun v => (base I p t k b n hM).runEncoded G (input G R B c) v = true) =
      surfaceIntegralOutput G I p t k b n hM R B c := by
  rfl
set_option maxHeartbeats 800000 in
theorem parameters (g M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℚ, ∃ p : GeneralCoveringFractionalErrorBudget.Parameters (3*(g : ℝ)+3) M (4*(δ : ℝ)/4),
      ∃ t k b n K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ g) →
      ∀ {ids : ℕ} (I : BitCode V ids) (R B : Finset V), Disjoint R B → ∀ c : V → Fin (M+1),
      (∀ r ∈ R, (rows G R B r).Nonempty) → (∀ v ∈ B, 1 ≤ (c v).val) →
      let D := Finset.univ.filter (fun v => (program I p t k b n (3*g+3) K hM).runEncoded G (input G R B c) v = true)
      GeneralCoveringIntegral.Covers (rows G R B) R D ∧
      ((∑ v ∈ D, (c v).val : ℕ) : ℝ) ≤ (4+ε)*(IntegralCoverOptimum.optimum (rows G R B) R (fun v => (c v).val) : ℝ) := by
  obtain ⟨δ,hδ,hsmall,hK,hthreshold⟩ := AbsorptionPublicParameters.public_absorption_parameters 4 ε (M*g) (by norm_num) hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨p,t,k,b,n,ht,hk,hs⟩ := surface_integral_parameters g M hM (4*(δ : ℝ)) (by positivity)
  let K := max 1 (Nat.ceil (2*((M*g : ℕ) : ℝ)/ε))
  refine ⟨δ,p,t,k,b,n,K,?_⟩
  intro V _ _ G _ hrot ids I R B hRB c hrows hc
  have hb := hs G hrot I R B hRB c hrows hc
  obtain ⟨rot,hgen⟩ := hrot
  have hm := SurfaceRounding.minorDensity_of_signedRotation G rot (g : ℝ) (Nat.cast_nonneg _) hgen
  have hden : Incidence.InducedDensityBound G ((3*g+3 : ℕ) : ℝ) := by
    intro S
    have hh := hm (S : Set V) (G.induce (S : Set V)) (SimpleGraph.IsMinor.of_induce G _)
    simpa only [SimpleGraph.inducedEdgeCount,Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard,
      Nat.cast_add,Nat.cast_mul,add_comm] using hh
  have hl : ∀ r ∈ R, rows G R B r ⊆ SevenFoundation.closed G r := fun r _ => rows_local G R B r
  have hd := ComponentDensity.subgraph_density G (CoveringIncidence.graph (rows G R B) R)
    (CoveringIncidence.graph_le G _ _ hl) hden
  have hc0 : GeneralCoveringIntegral.Covers (rows G R B) R
      (Finset.univ.filter (fun v => (base I p t k b n hM).runEncoded G (input G R B c) v = true)) := by
    rw [base_correct]
    intro r hr
    obtain ⟨v,hv,hvB,hadj⟩ := hb.2.1 r hr
    exact ⟨v,hv,(mem_rows G R B r v).mpr ⟨hr,hadj,hvB⟩⟩
  have happ : (((Finset.univ.filter (fun v => (base I p t k b n hM).runEncoded G (input G R B c) v = true)).sum
      (fun v => (input G R B c v).cost.val) : ℕ) : ℝ) ≤
      4*(1+(δ : ℝ))*CoveringOptimum.number (rows G R B) R (fun v => ((input G R B c v).cost.val : ℝ))+(M*g : ℕ) := by
    rw [base_correct]
    simp only [input,Nat.cast_sum]
    have heq := GeneralCoveringNormalizedFractional.supportedNumber_eq_number (rows G R B) R
      (fun v => ((c v).val : ℝ)) hrows (fun v => Nat.cast_nonneg _)
    rw [heq] at hb
    simp only [Nat.cast_mul]
    nlinarith [hb.2.2]
  exact AbsorptionRuntimeBound.absorption_runtime_bound G (rows G R B) (targets G R B) R
    (targets_incidence G R B) hl (3*g+3) (by omega) hd M K hM I (input G R B c)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun v hv => hc v (admissible_subset_blue G R B hv)) hK hrows (base I p t k b n hM) hc0
    4 ε (M*g) δ (by norm_num) hε hδ hsmall hthreshold happ
end Paper.RedBlueSurfaceAbsorption
#print axioms Paper.RedBlueSurfaceAbsorption.parameters
