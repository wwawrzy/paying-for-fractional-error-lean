import Paper.Endpoints.Components.ActualReplacementGlobalCost
import Paper.Endpoints.Components.ActualComponentReplacement
import Paper.Endpoints.Components.CoverOptimumCost
set_option maxHeartbeats 200000
namespace Paper.AllSolvedGlobalOptimum

theorem all_solved_cost_eq_optimum
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
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => A0.runEncoded G s u = true)))
    (hall : ∀ v, ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s v).1 = true) :
    (Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)).sum
        (fun u => (s u).cost.val) =
    Paper.IntegralCoverOptimum.optimum cover R (fun u => (s u).cost.val) := by
  classical
  obtain ⟨O, hO, hEq⟩ := Paper.IntegralCoverOptimum.exists_optimal cover R
    (fun u => (s u).cost.val) hrows
  let AO : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool :=
    Paper.CoverOptimumCost.selectSet O
  have hAO : Finset.univ.filter (fun u => AO.runEncoded G s u = true) = O :=
    Paper.CoverOptimumCost.selectSet_output G O s
  have hcovAO : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => AO.runEncoded G s u = true)) := by
    rw [hAO]
    exact hO.2
  have hbound := Paper.ActualReplacementGlobalCost.replacement_cost_le G cover targets R hinc hlocal
    a ha hden B K hB ids s hd hC ht hc hK hrows AO hcovAO
  have hout (A : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool) :
      Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A
        (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true) =
      Finset.univ.filter (fun u => ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s u).2 = true) := by
    rw [Paper.ComponentReplacementProgram.run_encoded]
    apply Finset.ext
    intro u
    simp [hall u]
  have hsame := (hout A0).trans (hout AO).symm
  rw [← hsame, hAO] at hbound
  apply Nat.le_antisymm (hbound.trans hEq.le)
  exact Paper.CoverOptimumCost.optimum_le_cover_cost cover R _ (fun u => (s u).cost.val)
    (Paper.ActualComponentReplacement.replacement_covers G cover targets R hinc hlocal
      a ha hden B K hB ids s hd hC ht hc hK hrows A0 hcover0)

end Paper.AllSolvedGlobalOptimum

#print axioms Paper.AllSolvedGlobalOptimum.all_solved_cost_eq_optimum
