import Paper.Endpoints.Rounding.AbsorptionRuntimeBound
import Paper.Endpoints.Components.ComponentDensity
import Paper.Endpoints.Rounding.NoncriticalOptimum
namespace Paper.OrdinaryAbsorption
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
def lift (A : Program V Unit Bool) : Program V (GeneralCoveringFractional.Input V 1) Bool :=
  .seq (.local fun _ _ _ => ()) A
noncomputable def program {bits : ℕ} (ids : BitCode V bits) (a K : ℕ)
    (A : Program V Unit Bool) :=
  ComponentReplacementProgram.program (lift A) (SmallComponentProgram.program ids a 1 K (by omega))
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def input (v : V) : GeneralCoveringFractional.Input V 1 :=
  ⟨true,1,true,closed G v,closed G v⟩
theorem covers_iff (D : Finset V) :
    GeneralCoveringIntegral.Covers (closed G) Finset.univ D ↔ dominates G D := by
  constructor
  · intro h v
    obtain ⟨u,hu,hvu⟩ := h v (Finset.mem_univ v)
    exact Finset.mem_biUnion.mpr ⟨u,hu,(closed_symm G u v).mp hvu⟩
  · intro h v _
    obtain ⟨u,hu,huv⟩ := Finset.mem_biUnion.mp (h v)
    exact ⟨u,hu,(closed_symm G v u).mp huv⟩
theorem number_eq : CoveringOptimum.number (closed G) Finset.univ (fun _ => (1:ℝ)) = fractionalNumber G := by
  rw [← NoncriticalOptimum.number_eq G]
  rfl
set_option maxHeartbeats 400000 in
theorem endpoint {bits : ℕ} (ids : BitCode V bits) (a K : ℕ) (ha : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (hK : 1 ≤ K)
    (A : Program V Unit Bool) (r ε : ℝ) (q : ℕ) (δ : ℚ)
    (hr : 1 ≤ r) (hε : 0 < ε) (hδ : 0 < δ) (hsmall : (δ : ℝ) ≤ ε/(2*r))
    (hthreshold : 2*(q : ℝ)/ε ≤ (K : ℝ))
    (hcover : dominates G (Finset.univ.filter (fun v => A.run G (fun _ => ()) v = true)))
    (hcost : ((Finset.univ.filter (fun v => A.run G (fun _ => ()) v = true)).card : ℝ) ≤
      r*(1+(δ : ℝ))*fractionalNumber G+q) :
    let Z := Finset.univ.filter (fun v => (program ids a K A).runEncoded G (input G) v = true)
    dominates G Z ∧ ∀ Y : Finset V, dominates G Y → (Z.card : ℝ) ≤ (r+ε)*Y.card := by
  classical
  have hi : ∀ v u, u ∈ closed G v ↔ v ∈ closed G u := fun v u => (closed_symm G v u).symm
  have hlocal : ∀ v ∈ (Finset.univ : Finset V), closed G v ⊆ closed G v := fun _ _ => Finset.Subset.refl _
  have hd := ComponentDensity.subgraph_density G (CoveringIncidence.graph (closed G) Finset.univ)
    (CoveringIncidence.graph_le G (closed G) Finset.univ hlocal) hden
  have hrows : ∀ v ∈ (Finset.univ : Finset V), (closed G v).Nonempty :=
    fun v _ => ⟨v,self_mem_closed G v⟩
  have hlift : (lift A).runEncoded G (input G) = A.run G (fun _ => ()) := by
    rw [Program.runEncoded_eq_run]; rfl
  have hc0 : GeneralCoveringIntegral.Covers (closed G) Finset.univ
      (Finset.univ.filter (fun v => (lift A).runEncoded G (input G) v = true)) := by
    rw [hlift]; exact (covers_iff G _).mpr hcover
  have hb0 : (((Finset.univ.filter (fun v => (lift A).runEncoded G (input G) v = true)).sum
      (fun u => (input G u).cost.val) : ℕ) : ℝ) ≤
      r*(1+(δ : ℝ))*CoveringOptimum.number (closed G) Finset.univ
        (fun u => ((input G u).cost.val : ℝ)) + (q : ℝ) := by
    simpa [hlift,input,number_eq G] using hcost
  have h := AbsorptionRuntimeBound.absorption_runtime_bound G (closed G) (closed G) Finset.univ
    hi hlocal a ha hd 1 K (by omega) ids (input G)
    (by intro v; simp [input]) (by intro v; rfl) (by intro v; rfl)
    (by intro v hv; norm_num [input]) hK hrows (lift A) hc0 r ε q δ hr hε hδ hsmall hthreshold hb0
  dsimp only at h ⊢
  refine ⟨(covers_iff G _).mp h.1,?_⟩
  intro Y hY
  have hadm : Y ⊆ CoveringSupport.admissible (closed G) Finset.univ := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ v,self_mem_closed G v⟩
  have ho := IntegralCoverOptimum.optimum_le_cost (closed G) Finset.univ (fun _ => 1)
    ⟨hadm,(covers_iff G Y).mpr hY⟩
  have ho' : (IntegralCoverOptimum.optimum (closed G) Finset.univ (fun _ => 1) : ℝ) ≤ Y.card := by
    exact_mod_cast (show IntegralCoverOptimum.optimum (closed G) Finset.univ (fun _ => 1) ≤ Y.card by simpa [IntegralCoverOptimum.cost] using ho)
  have hh : ((Finset.univ.filter (fun v => (program ids a K A).runEncoded G (input G) v = true)).card : ℝ) ≤
      (r+ε)*(IntegralCoverOptimum.optimum (closed G) Finset.univ (fun _ => 1) : ℝ) := by
    simpa [program,input] using h.2
  exact hh.trans (mul_le_mul_of_nonneg_left ho' (by linarith))
end Paper.OrdinaryAbsorption
#print axioms Paper.OrdinaryAbsorption.endpoint
