import Paper.Communication.SurfaceResidualInput
import Paper.Endpoints.Components.SurfaceComponentCases
namespace Paper.SurfaceResidual
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

theorem union_dominates (D : Finset V)
    (hD : GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d) D) :
    dominates G (CurrentBudget.selected G d ∪ D) := by
  intro v
  by_cases hv : v ∈ covered G (CurrentBudget.selected G d)
  · obtain ⟨u, hu, huv⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ hu, huv⟩
  · have hr : v ∈ CurrentBudget.demands G d := by
      simp [CurrentBudget.demands, hv]
    obtain ⟨u, hu, huv⟩ := hD v hr
    have hclosed : u ∈ closed G v := (Finset.mem_inter.mp huv).1
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_right _ hu,
      (closed_symm G v u).mpr hclosed⟩


theorem prepared_cases (a K : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (cover G d) (CurrentBudget.demands G d)) (a : ℝ))
    {bits : ℕ} (ids : BitCode V bits)
    (A0 : Program V (GeneralCoveringFractional.Input V 1) Bool)
    (hcover0 : GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true))) :
    (Finset.univ.filter (fun u => (ComponentReplacementProgram.program A0
      (SmallComponentProgram.program ids a 1 K (by omega))).runEncoded G (unitInput G d) u = true)).card =
        IntegralCoverOptimum.optimum (cover G d) (CurrentBudget.demands G d) (fun _ => 1) ∨
    K < (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true)).card := by
  exact SurfaceComponentCases.actual_cases G (cover G d) (targets G d)
    (CurrentBudget.demands G d) (incidence G d)
    (fun r _ => cover_local G d r) a ha hden 1 K (by omega) ids
    (unitInput G d) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => by change 1 ≤ (1 : ℕ); omega) hK (rows_nonempty G d) A0 hcover0 (unitInput_cost G d)

theorem prepared_card_le (a K : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (cover G d) (CurrentBudget.demands G d)) (a : ℝ))
    {bits : ℕ} (ids : BitCode V bits)
    (A0 : Program V (GeneralCoveringFractional.Input V 1) Bool)
    (hcover0 : GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true))) :
    (Finset.univ.filter (fun u => (ComponentReplacementProgram.program A0
      (SmallComponentProgram.program ids a 1 K (by omega))).runEncoded G (unitInput G d) u = true)).card ≤
    (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true)).card := by
  have h := ActualReplacementGlobalCost.replacement_cost_le G (cover G d) (targets G d)
    (CurrentBudget.demands G d) (incidence G d)
    (fun r _ => cover_local G d r) a ha hden 1 K (by omega) ids
    (unitInput G d) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => by change 1 ≤ (1 : ℕ); omega) hK (rows_nonempty G d) A0 hcover0
  simpa only [unitInput_cost, Finset.sum_const, smul_eq_mul, mul_one] using h

theorem prepared_covers (a K : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (cover G d) (CurrentBudget.demands G d)) (a : ℝ))
    {bits : ℕ} (ids : BitCode V bits)
    (A0 : Program V (GeneralCoveringFractional.Input V 1) Bool)
    (hcover0 : GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true))) :
    GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun u => (ComponentReplacementProgram.program A0
        (SmallComponentProgram.program ids a 1 K (by omega))).runEncoded G (unitInput G d) u = true)) := by
  exact ActualComponentReplacement.replacement_covers G (cover G d) (targets G d)
    (CurrentBudget.demands G d) (incidence G d)
    (fun r _ => cover_local G d r) a ha hden 1 K (by omega) ids
    (unitInput G d) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => by change 1 ≤ (1 : ℕ); omega) hK (rows_nonempty G d) A0 hcover0

theorem prepared_dominates (a K : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hden : Incidence.InducedDensityBound
      (CoveringIncidence.graph (cover G d) (CurrentBudget.demands G d)) (a : ℝ))
    {bits : ℕ} (ids : BitCode V bits)
    (A0 : Program V (GeneralCoveringFractional.Input V 1) Bool)
    (hcover0 : GeneralCoveringIntegral.Covers (cover G d) (CurrentBudget.demands G d)
      (Finset.univ.filter (fun u => A0.runEncoded G (unitInput G d) u = true))) :
    dominates G (CurrentBudget.selected G d ∪
      Finset.univ.filter (fun u => (ComponentReplacementProgram.program A0
        (SmallComponentProgram.program ids a 1 K (by omega))).runEncoded G (unitInput G d) u = true)) := by
  exact union_dominates G d _ (prepared_covers G d a K ha hK hden ids A0 hcover0)

end Paper.SurfaceResidual
