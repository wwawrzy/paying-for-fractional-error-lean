import Paper.Endpoints.Components.AllSolvedGlobalOptimum
import Paper.Endpoints.Components.UnsolvedGlobalOptimum
namespace Paper.SurfaceComponentCases
theorem actual_cases
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
    (hunit : ∀ v, (s v).cost.val = 1) :
    (Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)).card =
        Paper.IntegralCoverOptimum.optimum cover R (fun _ => 1) ∨
    K < (Finset.univ.filter (fun u => A0.runEncoded G s u = true)).card := by
  classical
  by_cases hall : ∀ v, ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s v).1 = true
  · left
    have h := Paper.AllSolvedGlobalOptimum.all_solved_cost_eq_optimum G cover targets R
      hinc hlocal a ha hden B K hB ids s hd hC ht hc hK hrows A0 hcover0 hall
    simpa only [hunit, Finset.sum_const, smul_eq_mul, mul_one] using h
  · right
    push Not at hall
    obtain ⟨v, hv⟩ := hall
    have h := Paper.UnsolvedGlobalOptimum.unsolved_implies_large_global_optimum
      G cover targets R hinc hlocal a ha hden B K hB ids s hd hC ht
      ((Paper.CoveringIncidence.graph cover R).connectedComponentMk v)
      hc hK hrows v (by simp) hv
    have hb := Paper.CoverOptimumCost.optimum_le_cover_cost cover R _
      (fun u => (s u).cost.val) hcover0
    have hcard := h.trans_le hb
    simpa only [hunit, Finset.sum_const, smul_eq_mul, mul_one] using hcard

end Paper.SurfaceComponentCases
