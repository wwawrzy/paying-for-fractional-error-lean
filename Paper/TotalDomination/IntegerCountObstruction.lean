import Paper.TotalDomination.IntegerSelectedCount
import Paper.Endpoints.Girth.HighGirthMinorPaths

/-! A checked obstruction to fv:total:count when its coefficient kappa is
allowed to be negative. This does not modify the paper or assume an axiom. -/
namespace Paper.TotalDomination.IntegerCountObstruction
open SevenFoundation IntegerSetup

def graph : SimpleGraph (Fin 2) := ⊤
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 2)).Adj)

theorem degree (v : Fin 2) : graph.degree v = 1 := by fin_cases v <;> decide

theorem free : ∀ v, (graph.neighborFinset v).Nonempty := by
  intro v
  apply Finset.card_pos.mp
  simp only [SimpleGraph.card_neighborFinset_eq_degree,degree]
  decide

theorem density : MinorDensity.Bound graph 1 := by
  have heq : PathPowerTreewidth.graph 2 1 = graph := by
    ext u v
    simp only [PathPowerTreewidth.graph,graph,SimpleGraph.top_adj]
    constructor
    · exact fun h => h.1
    · intro h;refine ⟨h,?_,?_⟩ <;> omega
  rw [← heq]
  exact HighGirthMinorPaths.density 2 1 le_rfl

theorem selected_empty : InitialSelection.selected graph 2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := WeightedBudget.far_degree graph 2 (InitialSelection.selected_subset_far graph 2 hv)
  rw [degree] at h
  omega

theorem remaining_univ : Z graph 2 = Finset.univ := by simp [Z,InitialSelection.remaining,selected_empty]
theorem cost_two (v : Fin 2) : c graph 2 v = 2 := by simp [c,InitialSelection.boundaryCost,InitialSelection.hits,selected_empty]
theorem candidates_univ : K graph 2 = Finset.univ := by simp [K,InitialSelection.candidates,cost_two]
theorem linked_empty : linked graph 2 = ∅ := by simp [linked,F,selected_empty,neighbors]
theorem demands_univ : demands graph 2 = Finset.univ := by simp [demands,remaining_univ,linked_empty]
theorem eligible_empty : eligible graph 2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (Finset.mem_filter.mp hv).2
  rw [degree] at h
  omega

variable (x : Fin 2 → ℝ) (id : Fin 2 → ℕ)

theorem first_empty : first graph (I graph 2 x id free) = ∅ := by
  simp only [first,I,input,eligible_empty,Finset.filter_empty]
theorem residual_univ : residual graph (I graph 2 x id free) = Finset.univ := by
  change demands graph 2 \ neighbors graph (first graph (I graph 2 x id free)) = _
  simp only [first_empty,demands_univ,neighbors,Finset.biUnion_empty,Finset.sdiff_empty]
theorem hits_one (v : Fin 2) : hits graph (I graph 2 x id free) v = 1 := by
  simp only [hits,residual_univ,Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree,degree]
theorem high_empty : high graph (I graph 2 x id free) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (Finset.mem_filter.mp hv).2
  change 2 ≤ hits graph (I graph 2 x id free) v at h
  rw [hits_one] at h
  omega

theorem core_empty : core graph 2 x id free = ∅ := by simp only [core,high_empty,Finset.empty_inter]
theorem served_low_empty : servedLow graph 2 x id free = ∅ := by
  simp [servedLow,served,high_empty,neighbors]
theorem uniform_charge (κ : ℝ) :
    ((WeightedBudget.defects graph 2 ∩ core graph 2 x id free).card : ℝ) ≤
      κ*((servedLow graph 2 x id free).card+(first graph (I graph 2 x id free)).card) := by
  simp only [core_empty,served_low_empty,first_empty,Finset.inter_empty,Finset.card_empty,Nat.cast_zero,zero_add,mul_zero,le_refl]

theorem feasible_one : CoveringOptimum.Feasible (fun r => graph.neighborFinset r) (Z graph 2) (fun _ => (1:ℝ)) := by
  constructor
  · intro v;norm_num
  · intro r _
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,SimpleGraph.card_neighborFinset_eq_degree,degree,Nat.cast_one]
    exact le_rfl

theorem penalty_one : penalty graph (I graph 2 (fun _ => 1) id free) (fun v => (c graph 2 v : ℝ)) = 2 := by
  have ho : other graph (I graph 2 (fun _ => 1) id free) = Finset.univ := by
    simp only [other,first_empty,high_empty,Finset.union_empty,Finset.sdiff_empty]
    exact candidates_univ
  rw [penalty,ho]
  change (∑ v : Fin 2, ((c graph 2 v : ℝ)-(hits graph (I graph 2 (fun _ => 1) id free) v : ℝ))*1) = 2
  simp only [cost_two,hits_one,Nat.cast_ofNat,mul_one]
  norm_num

theorem oversupply_one : oversupply graph (I graph 2 (fun _ => 1) id free) = 0 := by
  simp only [oversupply,I,input,Finset.sum_const,nsmul_eq_mul,mul_one,
    SimpleGraph.card_neighborFinset_eq_degree,degree,Nat.cast_one,sub_self,Finset.sum_const_zero,mul_zero]

theorem surplus_one : surplus graph (I graph 2 (fun _ => 1) id free) = 0 := by
  simp [surplus,served,high_empty,neighbors]

/-- At d=2,kappa=-2 the printed right-hand side is -56 although the uniform
hypothesis on defect counts holds for every input vector. -/
theorem negative_coefficient_fails :
    ¬ ((output graph (I graph 2 (fun _ => 1) id free)).card : ℝ) ≤
      (1+7*(-2:ℝ)+(-7)*2*(2+2)/2)*(first graph (I graph 2 (fun _ => 1) id free)).card +
      (-7:ℝ)*2^2/2*surplus graph (I graph 2 (fun _ => 1) id free) +
      (2*(2-1)*7+(-7)*(2-1)*(2^2+2):ℝ)*penalty graph (I graph 2 (fun _ => 1) id free) (fun v => (c graph 2 v : ℝ)) +
      (-7:ℝ)*2*oversupply graph (I graph 2 (fun _ => 1) id free) := by
  rw [first_empty,surplus_one,penalty_one,oversupply_one]
  have hn : (0:ℝ) ≤ (output graph (I graph 2 (fun _ => 1) id free)).card := Nat.cast_nonneg _
  norm_num
  linarith

end Paper.TotalDomination.IntegerCountObstruction
#print axioms Paper.TotalDomination.IntegerCountObstruction.negative_coefficient_fails
#print axioms Paper.TotalDomination.IntegerCountObstruction.uniform_charge
#print axioms Paper.TotalDomination.IntegerCountObstruction.density
