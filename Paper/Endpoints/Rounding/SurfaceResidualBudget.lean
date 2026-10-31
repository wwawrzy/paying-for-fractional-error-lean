import Paper.Endpoints.Rounding.CurrentBudget
import Paper.Endpoints.Components.IntegralCoverOptimum
/-! Actual integral and unit-cost budgets for the residual covering instance.
These are mathematical benchmarks; no optimum is supplied to the runtime. -/
namespace Paper.SurfaceResidual
open SevenFoundation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
noncomputable def cover (r : V) : Finset V := (CurrentBudget.auxiliary G d).eligible r
noncomputable def costNat (v : V) : ℕ :=
  d+1-(closed G v ∩ CurrentBudget.selected G d).card

theorem costNat_eq {v : V} (hv : v ∈ CurrentBudget.candidates G d) :
    (costNat G d v:ℝ)=CurrentBudget.boundaryCost G d v := by
  have hh:=CurrentBudget.boundary_card_le G d hv
  unfold costNat CurrentBudget.boundaryCost
  rw [Nat.cast_sub (by omega)]

theorem admissible_subset : CoveringSupport.admissible (cover G d) (CurrentBudget.demands G d) ⊆
    CurrentBudget.candidates G d := by
  intro v hv
  obtain ⟨r,hr,hv⟩:=Finset.mem_biUnion.mp hv
  exact Finset.mem_inter.mp hv |>.2

theorem rows_nonempty : ∀ r ∈ CurrentBudget.demands G d, (cover G d r).Nonempty := by
  intro r hr
  refine ⟨r,Finset.mem_inter.mpr ⟨self_mem_closed G r,?_⟩⟩
  exact CurrentBudget.demands_subset_candidates G d hr

theorem restricted_cover (Y : Finset V) (hY : dominates G Y) :
    IntegralCoverOptimum.Feasible (cover G d) (CurrentBudget.demands G d)
      (Y ∩ CoveringSupport.admissible (cover G d) (CurrentBudget.demands G d)) := by
  refine ⟨Finset.inter_subset_right,?_⟩
  intro r hr
  obtain ⟨v,hvY,hrv⟩:=Finset.mem_biUnion.mp (hY r)
  have hvclosed : v ∈ closed G r := (closed_symm G r v).mp hrv
  have hvC := CurrentBudget.demand_closed_subset_candidates G d hr hvclosed
  have hvel : v ∈ cover G d r := Finset.mem_inter.mpr ⟨hvclosed,hvC⟩
  exact ⟨v,Finset.mem_inter.mpr ⟨hvY,Finset.mem_biUnion.mpr ⟨r,hr,hvel⟩⟩,hvel⟩

theorem integral_budget (Y : Finset V) (hY : dominates G Y) :
    (CurrentBudget.selected G d).card+
      IntegralCoverOptimum.optimum (cover G d) (CurrentBudget.demands G d) (costNat G d) ≤
      (d+1)*Y.card := by
  have hb:=CurrentBudget.weighted_budget G d (indicator Y) (indicator_feasible G Y hY)
  have hsum : (∑ v ∈ CurrentBudget.candidates G d, CurrentBudget.boundaryCost G d v*indicator Y v)=
      ((∑ v ∈ Y ∩ CurrentBudget.candidates G d,costNat G d v:ℕ):ℝ) := by
    simp only [Nat.cast_sum]
    calc
      _ = ∑ v ∈ CurrentBudget.candidates G d, if v ∈ Y then CurrentBudget.boundaryCost G d v else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [indicator,mul_ite,mul_one,mul_zero]
      _ = ∑ v ∈ (CurrentBudget.candidates G d).filter (fun v=>v ∈ Y), CurrentBudget.boundaryCost G d v := by
        rw [Finset.sum_filter]
      _ = ∑ v ∈ Y ∩ CurrentBudget.candidates G d, (costNat G d v:ℝ) := by
        have he : (CurrentBudget.candidates G d).filter (fun v=>v ∈ Y)=Y ∩ CurrentBudget.candidates G d := by ext v;simp [and_comm]
        rw [he]
        apply Finset.sum_congr rfl
        intro v hv
        exact (costNat_eq G d (Finset.mem_inter.mp hv).2).symm
  have hcard : (∑ v, indicator Y v)=(Y.card:ℝ) := by simp [indicator]
  rw [hsum,hcard] at hb
  have ho := IntegralCoverOptimum.optimum_le_cost (cover G d) (CurrentBudget.demands G d)
    (costNat G d) (restricted_cover G d Y hY)
  have hs : IntegralCoverOptimum.cost (costNat G d)
      (Y ∩ CoveringSupport.admissible (cover G d) (CurrentBudget.demands G d)) ≤
      ∑ v ∈ Y ∩ CurrentBudget.candidates G d,costNat G d v := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.inter_subset_inter (Finset.Subset.refl Y) (admissible_subset G d)
  have hbo : (CurrentBudget.selected G d).card+
      (∑ v ∈ Y ∩ CurrentBudget.candidates G d,costNat G d v) ≤ (d+1)*Y.card := by exact_mod_cast hb
  omega
theorem costNat_pos {v : V} (hv : v ∈ CurrentBudget.candidates G d) :
    1 ≤ costNat G d v := by
  have h := CurrentBudget.boundary_card_le G d hv
  unfold costNat
  omega

theorem unit_optimum_le_weighted :
    IntegralCoverOptimum.optimum (cover G d) (CurrentBudget.demands G d) (fun _ => 1) ≤
      IntegralCoverOptimum.optimum (cover G d) (CurrentBudget.demands G d) (costNat G d) := by
  obtain ⟨D, hD, he⟩ := IntegralCoverOptimum.exists_optimal (cover G d)
    (CurrentBudget.demands G d) (costNat G d) (rows_nonempty G d)
  have hu := IntegralCoverOptimum.optimum_le_cost (cover G d)
    (CurrentBudget.demands G d) (fun _ => 1) hD
  have hc := IntegralCoverOptimum.card_le_cost (cover G d) (CurrentBudget.demands G d)
    (costNat G d) (fun v hv => costNat_pos G d (admissible_subset G d hv)) hD
  simp only [IntegralCoverOptimum.cost, Finset.sum_const, smul_eq_mul, mul_one] at hu
  exact hu.trans (hc.trans he.le)

/-- Exact cardinality budget for the residual instance of the surface algorithm. -/
theorem unit_budget (Y : Finset V) (hY : dominates G Y) :
    (CurrentBudget.selected G d).card +
      IntegralCoverOptimum.optimum (cover G d) (CurrentBudget.demands G d) (fun _ => 1) ≤
      (d + 1) * Y.card := by
  exact (Nat.add_le_add_left (unit_optimum_le_weighted G d) _).trans
    (integral_budget G d Y hY)

/-- The surface application uses degree six and therefore coefficient seven. -/
theorem surface_unit_budget (Y : Finset V) (hY : dominates G Y) :
    (CurrentBudget.selected G 6).card +
      IntegralCoverOptimum.optimum (cover G 6) (CurrentBudget.demands G 6) (fun _ => 1) ≤
      7 * Y.card := unit_budget G 6 Y hY

end Paper.SurfaceResidual
