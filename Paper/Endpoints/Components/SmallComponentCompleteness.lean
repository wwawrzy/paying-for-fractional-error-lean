import Paper.Endpoints.Components.SmallComponentSolvedCover
import Paper.Endpoints.Components.OptimumAcceptance

namespace Paper.SmallComponentCompleteness

theorem logical_small_optimum_solved
    {V : Type} [Fintype V] [LinearOrder V]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K)
    (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (hopt : Paper.IntegralCoverOptimum.optimum cover
      (R ∩ Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X)
      (fun u => (s u).cost.val) ≤ K)
    (v : V) (hv : v ∈ X.supp) :
    ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 = true := by
  let I := Paper.CoveringIncidence.graph cover R
  let H := Paper.IncidenceComponent.vertices I X
  have hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed I r := by
    intro r hr u hu
    exact Paper.CoveringIncidence.candidate_mem_closed cover R hr hu
  have hphysical := Paper.PhysicalComponentAcceptance.small_optimum I cover targets R
    hinc hlocal B s hd hC ht ids X K hK hrows hc hopt v hv
  rw [Paper.PhysicalComponentAcceptance.run_correct I cover targets R hinc hlocal B s
    hd hC ht ids (5 * K - 1)] at hphysical
  apply (Paper.SmallComponentSolvedCover.logical_solved_iff_cover cover targets R hinc
    a ha hden B K hB ids s hd hC ht X hc v hv).mpr
  refine ⟨?_, ?_⟩
  · rw [Paper.SmallComponentProgram.acceptedInput_active]
    exact hphysical
  · obtain ⟨O, hO, hcost⟩ := (Paper.IntegralCoverOptimum.optimum_le_iff cover (R ∩ H)
      (fun u => (s u).cost.val) (fun r hr => hrows r (Finset.mem_inter.mp hr).1) K).mp hopt
    exact ⟨O, hO.1, hO.2, hcost⟩

end Paper.SmallComponentCompleteness

#print axioms Paper.SmallComponentCompleteness.logical_small_optimum_solved
