import Paper.Endpoints.Rounding.SurfaceShell
import Paper.Endpoints.Rounding.SurfaceIncidence
namespace Paper.SurfaceRounding
open SevenFoundation
attribute [local instance] Classical.propDecidable Classical.decEq
def MinorBound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj],
    SimpleGraph.IsMinor J G → (J.edgeFinset.card:ℝ) ≤ 3*Fintype.card W+3*e
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ)
variable (hx : feasible (CurrentBudget.auxiliary G 6) x)
variable (hcap : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1)
local notation "I" => CurrentCounting.input G 3 6 (by norm_num) x hx hcap
local notation "W" => CurrentRounding.first G 3 I
local notation "R" => CurrentRounding.residual G 3 I
local notation "Q" => CurrentRounding.overlap G 3 I
local notation "L" => CurrentRounding.middle G 3 I
local notation "U" => CurrentRounding.last G 3 I
local notation "B" => WeightedBudget.defects G 6 ∩ Q
local notation "f" => ComponentMinor.vertex G R W
local notation "K" => ComponentMinor.graph G R W
local notation "A" => ComponentMinor.contracted G R W
theorem overlap_surface (e : ℝ) (hden : MinorBound G e) :
    ((Q).card:ℝ) ≤ 48*((W).card+(L).card+(U).card)+48*e := by
  have hQR := CurrentCountBound.overlap_subset_residual G 3 6 (by norm_num) x hx hcap
  have hLR := CurrentCountBound.middle_subset_residual G 3 6 (by norm_num) x hx hcap
  have hUR := CurrentCountBound.last_subset_residual G 3 6 (by norm_num) x hx hcap
  have hrestR : L ∪ U ⊆ R := Finset.union_subset hLR hUR
  have hBQ : (B).image f ⊆ (Q).image f := Finset.image_subset_image Finset.inter_subset_right
  have hQT : Disjoint ((Q).image f) (A ∪ (L ∪ U).image f) := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨(ComponentMinor.contracted_disjoint_residual G R W Q hQR).symm,
      CurrentCountBound.image_disjoint_residual G 3 6 (by norm_num) x hx hcap Q (L ∪ U) hQR hrestR
        (CurrentCountBound.overlap_disjoint_rest G 3 6 (by norm_num) x hx hcap)⟩
  have hKD := hden _ K (ComponentMinor.isMinor G R W)
  have hKD' : 2*((K).edgeFinset.card:ℝ) ≤ 6*Fintype.card (ComponentMinor.retained G R W)+6*e := by linarith
  have hh := regular_shell_count K 6 (6*e)
    (A ∪ (L ∪ U).image f) ((Q).image f) ((B).image f) hBQ hQT
    (CurrentCountBound.minor_regular_off G 3 6 (by norm_num) x hx hcap)
    (CurrentCountBound.minor_defect_degree G 3 6 (by norm_num) x hx hcap)
    (CurrentCountBound.minor_regular_overlap_touch G 3 6 (by norm_num) x hx hcap) hKD'
  have hQcard := ComponentMinor.card_image_residual G R W Q hQR
  rw [hQcard] at hh
  have hT : (A ∪ (L ∪ U).image f).card ≤ (W).card + (L).card + (U).card := by
    have h1 := Finset.card_union_le A ((L ∪ U).image f)
    have h2 := ComponentMinor.contracted_card_le G R W
    have h3 : ((L ∪ U).image f).card ≤ (L ∪ U).card := Finset.card_image_le
    have h4 := Finset.card_union_le L U
    omega
  have hTR : ((A ∪ (L ∪ U).image f).card:ℝ) ≤ (W).card+(L).card+(U).card := by exact_mod_cast hT
  norm_num at hh
  nlinarith only [hh.2,hTR]




theorem induced_density (e : ℝ) (hden : MinorBound G e) :
    ∀ S : Finset V, (G.inducedEdgeCount S:ℝ) ≤ 3*S.card+3*e := by
  intro S
  have h := hden (S:Set V) (G.induce (S:Set V)) (SimpleGraph.IsMinor.of_induce G _)
  simpa only [SimpleGraph.inducedEdgeCount,Fintype.card_eq_nat_card,
    Finset.coe_sort_coe,Nat.card_eq_finsetCard] using h

theorem actual_bounds (e : ℝ) (he : 0 ≤ e) (hden : MinorBound G e) :
    ((W).card+(L).card:ℝ)/4+CurrentRounding.slack G 3 I-3/2*e ≤
      CurrentRounding.objective G 3 I-(CurrentRounding.output G 3 I).card ∧
    ((CurrentRounding.output G 3 I).card:ℝ) ≤ 49*((W).card+(L).card)+294*CurrentRounding.slack G 3 I+99/2*e ∧
    (1+1/294:ℝ)*(CurrentRounding.output G 3 I).card ≤ CurrentRounding.objective G 3 I+2*e := by
  have hex := excess_additive G 3 I (3*e) (induced_density G e hden)
  have hE0 : 0 ≤ CurrentRounding.excess G 3 I := by
    unfold CurrentRounding.excess
    apply Finset.sum_nonneg
    intro v hv
    exact sub_nonneg.mpr (Finset.mem_filter.mp hv).2
  have hfull := CurrentCounting.high_full_cost G 3 6 (by norm_num) x hx hcap
  have hW := CurrentRounding.first_mass_lower G 3 I
  have hR := CurrentRounding.coverage_sum G 3 I R (CurrentRounding.residual_subset G 3 I)
  change ((R).card:ℝ) ≤ ∑ v ∈ (I).candidates, (CurrentRounding.hits G 3 I v:ℝ)*(I).x v at hR
  have hE := CurrentRounding.weighted_excess_bound G 3 I hfull
  have hcost := CurrentRounding.cost_decomposition G 3 I hfull
  have hcard := CurrentRounding.output_card_identity G 3 I
  norm_num at hex hW hE hcost
  have hW' := mul_le_mul_of_nonneg_left hW (by norm_num : (0:ℝ) ≤ 7)
  have hs : ((W).card+(L).card:ℝ)/4+CurrentRounding.slack G 3 I-3/2*e ≤
      CurrentRounding.objective G 3 I-(CurrentRounding.output G 3 I).card := by
    linarith
  have hz : ((CurrentRounding.outside G 3 I).card:ℝ) ≤ (L).card+3/2*e := by linarith
  have hq := overlap_surface G x hx hcap e hden
  have hu := CurrentCounting.last_le_slack G 3 6 (by norm_num) x hx hcap
  have hh : ((CurrentRounding.high G 3 I).card:ℝ)=(Q).card+(CurrentRounding.outside G 3 I).card := by
    exact_mod_cast CurrentRounding.high_card_split G 3 I
  have ho : ((CurrentRounding.output G 3 I).card:ℝ)=(W).card+(CurrentRounding.high G 3 I).card+(U).card := by
    exact_mod_cast CurrentRounding.output_card_split G 3 I
  have hb : ((CurrentRounding.output G 3 I).card:ℝ) ≤
      49*((W).card+(L).card)+294*CurrentRounding.slack G 3 I+99/2*e := by
    norm_num at hu
    linarith
  refine ⟨hs,hb,?_⟩
  have hw0 : (0:ℝ) ≤ (W).card := Nat.cast_nonneg _
  have hl0 : (0:ℝ) ≤ (L).card := Nat.cast_nonneg _
  linarith

end Paper.SurfaceRounding
#print axioms Paper.SurfaceRounding.actual_bounds
