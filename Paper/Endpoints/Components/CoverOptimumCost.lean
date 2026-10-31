import Paper.Endpoints.Components.OptimumCertificate
import Paper.Communication.EncodedProgram

/-! A possibly redundant cover still costs at least the true admissible optimum.
Natural nonnegative costs allow pruning superfluous vertices in the proof. -/
namespace Paper.CoverOptimumCost

/-- Proof-side comparator only; this is not supplied to the actual replacement runtime. -/
def selectSet {V In : Type} [DecidableEq V] (D : Finset V) :
    Paper.BroadcastModel.Program V In Bool :=
  .local (fun v _ _ => decide (v ∈ D))

theorem selectSet_output {V In : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (s : V → In) :
    Finset.univ.filter (fun v => (selectSet D).runEncoded G s v = true) = D := by
  ext v
  simp [selectSet, Paper.BroadcastModel.Program.runEncoded]

theorem optimum_le_cover_cost
    {V : Type} [Fintype V] [DecidableEq V]
    (cover : V → Finset V) (R D0 : Finset V) (c : V → Nat)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R D0) :
    Paper.IntegralCoverOptimum.optimum cover R c ≤ D0.sum c := by
  classical
  let D := D0 ∩ Paper.CoveringSupport.admissible cover R
  have hfeas : Paper.IntegralCoverOptimum.Feasible cover R D := by
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro r hr
    obtain ⟨u, hu0, hur⟩ := hcover0 r hr
    exact ⟨u, Finset.mem_inter.mpr ⟨hu0, Finset.mem_biUnion.mpr ⟨r, hr, hur⟩⟩, hur⟩
  apply (Paper.IntegralCoverOptimum.optimum_le_cost cover R c hfeas).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
    (by intros; exact Nat.zero_le _)

end Paper.CoverOptimumCost

#print axioms Paper.CoverOptimumCost.optimum_le_cover_cost

#print axioms Paper.CoverOptimumCost.selectSet_output
