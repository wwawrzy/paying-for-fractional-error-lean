import Paper.Endpoints.Components.ActualComponentReplacement
import Paper.Endpoints.Components.ActualReplacementGlobalCost
import Paper.Endpoints.Components.AllSolvedGlobalOptimum
import Paper.Endpoints.Components.UnsolvedGlobalOptimum
import Paper.Endpoints.Components.CoveringFractionalIntegral
import Paper.Endpoints.Rounding.AdditiveAbsorptionArithmetic
set_option maxHeartbeats 200000
namespace Paper.AbsorptionRuntimeBound

theorem absorption_runtime_bound
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
    (r epsilon : Real) (q : Nat) (delta : Rat)
    (hr : 1 ≤ r) (hepsilon : 0 < epsilon) (hdelta_pos : 0 < delta)
    (hdelta : (delta : Real) ≤ epsilon / (2 * r))
    (hthreshold : 2 * (q : Real) / epsilon ≤ (K : Real))
    (happrox : (((Finset.univ.filter (fun u => A0.runEncoded G s u = true)).sum
      (fun u => (s u).cost.val) : Nat) : Real) ≤
      r * (1 + (delta : Real)) * Paper.CoveringOptimum.number cover R
        (fun u => ((s u).cost.val : Real)) + (q : Real)) :
    let D := Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)
    Paper.GeneralCoveringIntegral.Covers cover R D ∧
      ((D.sum (fun u => (s u).cost.val) : Nat) : Real) ≤
        (r + epsilon) * (Paper.IntegralCoverOptimum.optimum cover R
          (fun u => (s u).cost.val) : Real) := by
  classical
    let I := Paper.CoveringIncidence.graph cover R
    let D0 := Finset.univ.filter (fun u => A0.runEncoded G s u = true)
    let D := Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)
    let tau := Paper.CoveringOptimum.number cover R (fun u => ((s u).cost.val : Real))
    let opt := Paper.IntegralCoverOptimum.optimum cover R (fun u => (s u).cost.val)
    change Paper.GeneralCoveringIntegral.Covers cover R D ∧
      ((D.sum (fun u => (s u).cost.val) : Nat) : Real) ≤ (r + epsilon) * (opt : Real)
    refine ⟨Paper.ActualComponentReplacement.replacement_covers G cover targets R hinc hlocal
      a ha hden B K hB ids s hd hC ht hc hK hrows A0 hcover0, ?_⟩
    have hbound := Paper.ActualReplacementGlobalCost.replacement_cost_le G cover targets R hinc hlocal
      a ha hden B K hB ids s hd hC ht hc hK hrows A0 hcover0
    have htau := Paper.CoveringFractionalIntegral.fractional_nonneg_le_integral cover R
      (fun u => (s u).cost.val) hrows
    have hdeltaR : 0 < (delta : Real) := by exact_mod_cast hdelta_pos
    apply Paper.AdditiveAbsorptionArithmetic.absorption_bound r epsilon (delta : Real) tau (opt : Real) (q : Real)
      (((D.sum (fun u => (s u).cost.val) : Nat) : Real))
      (((D0.sum (fun u => (s u).cost.val) : Nat) : Real)) K
      hr hepsilon hdeltaR hdelta htau.1 htau.2 (Nat.cast_nonneg q) (Nat.cast_nonneg _) ?_
      happrox hthreshold ?_
    · exact_mod_cast hbound
    · by_cases hall : ∀ v, ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s v).1 = true
      · left
        exact_mod_cast (Paper.AllSolvedGlobalOptimum.all_solved_cost_eq_optimum G cover targets R
          hinc hlocal a ha hden B K hB ids s hd hC ht hc hK hrows A0 hcover0 hall)
      · right
        obtain ⟨v, hv⟩ := not_forall.mp hall
        have hlarge := Paper.UnsolvedGlobalOptimum.unsolved_implies_large_global_optimum G cover targets R
          hinc hlocal a ha hden B K hB ids s hd hC ht (I.connectedComponentMk v) hc hK hrows v (by rfl) hv
        exact_mod_cast hlarge

end Paper.AbsorptionRuntimeBound

#print axioms Paper.AbsorptionRuntimeBound.absorption_runtime_bound
