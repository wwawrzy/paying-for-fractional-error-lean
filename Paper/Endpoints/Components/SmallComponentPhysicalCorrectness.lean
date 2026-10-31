import Paper.Endpoints.Components.SmallComponentPhysicalCost
import Paper.Endpoints.Components.SmallComponentCompleteness
import Paper.Endpoints.Components.SmallComponentSolved

namespace Paper.SmallComponentPhysicalCorrectness

theorem physical_correct
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let out := (Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s
    (∀ v ∈ X.supp, ∀ u ∈ X.supp, (out v).1 = (out u).1) ∧
    (∀ v ∈ X.supp, (out v).1 = true →
      let D := H.filter (fun u => (out u).2 = true)
      Paper.IntegralCoverOptimum.Feasible cover (R ∩ H) D ∧
        Paper.IntegralCoverOptimum.cost (fun u => (s u).cost.val) D =
          Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val)) ∧
    (Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val) ≤ K →
      ∀ v ∈ X.supp, (out v).1 = true) ∧
    (∀ v, (out v).2 = true → (out v).1 = true) := by
  rw [Paper.SmallComponentProgram.physical_run G cover targets R hinc hlocal ids a B K hB s hd hC ht]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv u hu
    exact Paper.SmallComponentSolved.logical_solved_uniform cover targets R hinc a ha hden
      B K hB ids s hd hC ht X v u hv hu
  · intro v hv hsolved
    obtain ⟨hadm, hcover, _, _⟩ :=
      Paper.SmallComponentSelectedOptimal.logical_selected_optimal cover targets R hinc
        a ha hden B K hB ids s hd hC ht X hc v hv hsolved
    exact ⟨⟨hadm, hcover⟩,
      Paper.SmallComponentSelectedCost.logical_selected_cost_eq_optimum cover targets R hinc
        a ha hden B K hB ids s hd hC ht X hc v hv hsolved⟩
  · intro hopt v hv
    exact Paper.SmallComponentCompleteness.logical_small_optimum_solved cover targets R hinc
      a ha hden B K hB ids s hd hC ht X hc hK hrows hopt v hv
  · intro v hselected
    rw [Paper.SmallComponentProgram.logical_run] at hselected ⊢
    exact Paper.SmallComponentDecode.selected_implies_solved K v _ hselected

end Paper.SmallComponentPhysicalCorrectness

#print axioms Paper.SmallComponentPhysicalCorrectness.physical_correct
