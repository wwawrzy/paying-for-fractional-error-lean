import Paper.Endpoints.Components.SmallComponentPhysicalCorrectness
import Paper.Endpoints.Components.ComponentGlobalOptimum
set_option maxHeartbeats 200000
namespace Paper.UnsolvedGlobalOptimum

theorem unsolved_implies_large_global_optimum
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
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (v : V) (hv : v ∈ X.supp)
    (hunsolved : ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s v).1 ≠ true) :
    K < Paper.IntegralCoverOptimum.optimum cover R (fun u => (s u).cost.val) := by
  have hspec := Paper.SmallComponentPhysicalCorrectness.physical_correct G cover targets R
    hinc hlocal a ha hden B K hB ids s hd hC ht X hc hK hrows
  have hnot : ¬ Paper.IntegralCoverOptimum.optimum cover
      (R ∩ Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X)
      (fun u => (s u).cost.val) ≤ K := by
    intro hsmall
    exact hunsolved (hspec.2.2.1 hsmall v hv)
  exact lt_of_lt_of_le (lt_of_not_ge hnot)
    (Paper.ComponentGlobalOptimum.component_optimum_le_global cover R
      (fun u => (s u).cost.val) X hrows)

end Paper.UnsolvedGlobalOptimum

#print axioms Paper.UnsolvedGlobalOptimum.unsolved_implies_large_global_optimum
