import Paper.Endpoints.Girth.HighGirthChargeMultiplicity
set_option maxHeartbeats 200000
namespace Paper.HighGirthChargePacking

theorem component_positive_charge_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (family : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    (∑ K ∈ family, Paper.HighGirthPathCharges.positiveCharge G x K) ≤
      2 * Paper.HighGirthRounding.penalty G x := by
  classical
  let Pos := Paper.HighGirthRounding.positive G x
  let O := Paper.HighGirthRounding.other G x
  let gap := fun v => (Paper.HighGirthTransformation.candidateCost G v : Real) -
    (Paper.HighGirthRounding.hits G x v : Real)
  have hQ : ∀ K, Paper.HighGirthPathCharges.positiveCharge G x K =
      ∑ v ∈ Pos, if v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthFreePaths.members G x K) then x v else 0 := by
    intro K
    have heq : Pos ∩ Paper.SevenFoundation.covered G (Paper.HighGirthFreePaths.members G x K) =
        Pos.filter (fun v => v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthFreePaths.members G x K)) := by
      ext v
      simp
    change (∑ v ∈ Pos ∩ Paper.SevenFoundation.covered G (Paper.HighGirthFreePaths.members G x K), x v) = _
    rw [heq,Finset.sum_filter]
  have hdouble : (∑ K ∈ family, Paper.HighGirthPathCharges.positiveCharge G x K) =
      ∑ v ∈ Pos, ((Paper.HighGirthPathCharges.incidentComponents G x family v).card : Real) * x v := by
    simp_rw [hQ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp [Paper.HighGirthPathCharges.incidentComponents,nsmul_eq_mul]
  have hP : (∑ v ∈ Pos, x v) ≤ Paper.HighGirthRounding.penalty G x := by
    have hsub : Pos ⊆ O := fun v hv => (Finset.mem_filter.mp hv).1
    have hgap := (Paper.HighGirthSlack.slack_nonnegative G x hx).2.2
    calc
      _ ≤ ∑ v ∈ Pos, gap v * x v := by
        apply Finset.sum_le_sum
        intro v hv
        have hg : (1 : Real) ≤ gap v := (hgap v hv).1
        have hm := mul_le_mul_of_nonneg_right hg (hx.1 v)
        simpa using hm
      _ ≤ ∑ v ∈ O, gap v * x v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro v hv hn
        have hg := (Paper.HighGirthOtherGeometry.remaining_candidate_geometry G x v hv).1
        have hgReal : (Paper.HighGirthRounding.hits G x v : Real) ≤
            (Paper.HighGirthTransformation.candidateCost G v : Real) := by exact_mod_cast hg
        exact mul_nonneg (sub_nonneg.mpr hgReal) (hx.1 v)
      _ = Paper.HighGirthRounding.penalty G x := rfl
  calc
    _ = ∑ v ∈ Pos, ((Paper.HighGirthPathCharges.incidentComponents G x family v).card : Real) * x v := hdouble
    _ ≤ ∑ v ∈ Pos, 2 * x v := by
      apply Finset.sum_le_sum
      intro v hv
      have hn := (Paper.HighGirthChargeMultiplicity.positive_component_multiplicity G x family v hv).2
      have hr : ((Paper.HighGirthPathCharges.incidentComponents G x family v).card : Real) ≤ 2 := by exact_mod_cast hn
      exact mul_le_mul_of_nonneg_right hr (hx.1 v)
    _ = 2 * (∑ v ∈ Pos, x v) := by rw [Finset.mul_sum]
    _ ≤ 2 * Paper.HighGirthRounding.penalty G x := mul_le_mul_of_nonneg_left hP (by norm_num)

end Paper.HighGirthChargePacking

#print axioms Paper.HighGirthChargePacking.component_positive_charge_bound
