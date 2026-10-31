import Paper.Endpoints.Rounding.CurrentBudget
import Paper.Endpoints.Rounding.CurrentRounding
import Paper.Preliminaries.RadiusTwo
import Paper.Preliminaries.MinorDensity

/-!
Current `simp:endpoint:count`: genuine counting ingredients and the sharp
degree-sum core of the component-contraction argument.

The current budget (F = V \ N[B]) is instantiated below, not the older
distance-two budget. The current H\R and U estimates are proved, and the
sharp d(d+2) overlap count is proved for any graph with the structural
degree properties of the paper's component minor.

REMAINING BRIDGE: construct that component minor for these exact current
sets, prove regularity off A∪L∪U∪(B∩Q), and identify its retained Q/L/U
vertices. The old star-minor proof does not supply this: it contracts only
N[W] and uses the stronger distance-two regular region. Consequently this
file does not falsely label the full current endpoint or Main B proved.
No target counting or saving inequality is introduced as an assumption.
-/

namespace Paper.CurrentCounting

open SevenFoundation
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (d : ℕ)

/-- Sharp degree-sum core, applicable to the actual component minor once
its structural degree properties have been established. T is A∪L∪U;
B is the retained set of exceptional Q vertices. -/
theorem regular_shell_count (T Q B : Finset V)
    (hBQ : B ⊆ Q) (hQT : Disjoint Q T)
    (hregular : ∀ v ∉ T ∪ B, G.degree v = d)
    (hlarge : ∀ v ∈ B, d + 1 ≤ G.degree v)
    (htouch : ∀ v ∈ Q \ B, ∃ s ∈ T ∪ B, G.Adj v s)
    (hdensity : 2 * G.edgeFinset.card ≤ d * Fintype.card V) :
    B.card ≤ d * T.card ∧ Q.card ≤ d * (d + 2) * T.card := by
  classical
  let S := T ∪ B
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvB
    exact Finset.disjoint_left.mp hQT (hBQ hvB) hvT
  have hScard : S.card = T.card + B.card := Finset.card_union_of_disjoint hTB
  have hsum : ∑ s ∈ S, G.degree s ≤ d * S.card :=
    RadiusTwo.defect_degree_sum_le G S d hregular hdensity
  have hBsub : B ⊆ S := Finset.subset_union_right
  have hlower : (d + 1) * B.card ≤ ∑ s ∈ S, G.degree s := by
    calc
      _ = ∑ _v ∈ B, (d + 1) := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, G.degree v := Finset.sum_le_sum hlarge
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun _ _ _ => Nat.zero_le _)
  have hBcount : B.card ≤ d * T.card := by
    rw [hScard] at hsum
    nlinarith
  have hsub : Q \ B ⊆ RadiusTwo.shell G S := by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := htouch v hv
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨s, hs, (mem_closed G v s).mpr (Or.inr hvs.symm)⟩
    · intro hvS
      rcases Finset.mem_union.mp hvS with hvT | hvB
      · exact Finset.disjoint_left.mp hQT (Finset.mem_sdiff.mp hv).1 hvT
      · exact (Finset.mem_sdiff.mp hv).2 hvB
  have hrest : (Q \ B).card ≤ d * S.card :=
    (Finset.card_le_card hsub).trans ((RadiusTwo.shell_card_le G S).trans hsum)
  have hsplit := Finset.card_sdiff_add_card_eq_card hBQ
  have hmul := Nat.mul_le_mul_left (d + 1) hBcount
  rw [hScard] at hrest
  exact ⟨hBcount, by nlinarith⟩

/-- Minor-density input supplies the degree-sum premise of the sharp core.
All remaining assumptions describe vertex sets and degrees in an actual
minor, rather than assuming its desired cardinality estimate. -/
theorem minor_regular_shell_count {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj]
    (hden : MinorDensity.Bound G a) (hminor : SimpleGraph.IsMinor K G)
    (hd : (d : ℝ) = 2 * a) (T Q B : Finset W)
    (hBQ : B ⊆ Q) (hQT : Disjoint Q T)
    (hregular : ∀ v ∉ T ∪ B, K.degree v = d)
    (hlarge : ∀ v ∈ B, d + 1 ≤ K.degree v)
    (htouch : ∀ v ∈ Q \ B, ∃ s ∈ T ∪ B, K.Adj v s) :
    B.card ≤ d * T.card ∧ Q.card ≤ d * (d + 2) * T.card := by
  have hh := hden W K hminor
  have hreal : (2 : ℝ) * K.edgeFinset.card ≤ d * Fintype.card W := by
    rw [hd]
    linarith
  have hnat : 2 * K.edgeFinset.card ≤ d * Fintype.card W := by exact_mod_cast hreal
  exact regular_shell_count K d T Q B hBQ hQT hregular hlarge htouch hnat

variable (hd : (d : ℝ) = 2 * a) (x : V → ℝ)
variable (hx : feasible (CurrentBudget.auxiliary G d) x)
variable (hcap : ∀ v ∈ CurrentBudget.candidates G d, x v ≤ 1)

/-- The current weighted residual problem as the exact common-rounding input. -/
noncomputable def input : CurrentRounding.Input G a where
  candidates := CurrentBudget.candidates G d
  demands := CurrentBudget.demands G d
  demands_subset := CurrentBudget.demands_subset_candidates G d
  c := CurrentBudget.boundaryCost G d
  x := x
  cost_pos := by
    intro v hv
    exact zero_lt_one.trans_le (CurrentBudget.cost_integral_bounds G d hv).2.1
  cost_le := by
    intro v hv
    have hh := (CurrentBudget.cost_integral_bounds G d hv).2.2
    have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
    simpa only [hb] using hh
  nonneg := fun v _ => hx.1 v
  cap := hcap
  coverage := by
    intro r hr
    exact hx.2.2 r hr

local notation "I" => input G a d hd x hx hcap

theorem high_full_cost : ∀ v ∈ CurrentRounding.high G a I,
    CurrentBudget.boundaryCost G d v = 2 * a + 1 := by
  classical
  intro v hv
  have hvC : v ∈ CurrentBudget.candidates G d := CurrentRounding.high_subset G a I hv
  have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  have hupper := (CurrentBudget.cost_integral_bounds G d hvC).2.2
  apply le_antisymm (by simpa only [hb] using hupper)
  by_contra hn
  have hcheap : CurrentBudget.boundaryCost G d v < (d + 1 : ℕ) := by
    rw [hb]
    exact lt_of_not_ge hn
  have hcheapHits := CurrentBudget.cheap_closed_card G d hvC hcheap
  have hsub : closed G v ∩ CurrentRounding.residual G a I ⊆
      closed G v ∩ CurrentBudget.demands G d :=
    Finset.inter_subset_inter_left (CurrentRounding.residual_subset G a I)
  have hsmall : (CurrentRounding.hits G a I v : ℝ) ≤
      ((closed G v ∩ CurrentBudget.demands G d).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hlarge : 2 * a + 1 ≤ (CurrentRounding.hits G a I v : ℝ) :=
    (Finset.mem_filter.mp hv).2
  rw [hb] at hupper
  linarith

/-- Both pointwise estimates in the current paper's `endpoint:slack`.
They are proved from current candidate costs, not taken as hypotheses. -/
theorem other_slack : ∀ v ∈ CurrentRounding.other G a I,
    CurrentRounding.hits G a I v ≤ d ∧
      1 ≤ CurrentBudget.boundaryCost G d v - (CurrentRounding.hits G a I v : ℝ) := by
  classical
  intro v hv
  have hvC : v ∈ CurrentBudget.candidates G d := CurrentRounding.other_subset G a I hv
  have hnWH := (Finset.mem_sdiff.mp hv).2
  have hnW : v ∉ CurrentRounding.first G a I := fun h => hnWH (Finset.mem_union_left _ h)
  have hnH : v ∉ CurrentRounding.high G a I := fun h => hnWH (Finset.mem_union_right _ h)
  have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  have hc := (CurrentBudget.cost_integral_bounds G d hvC).2.2
  have hgap : 1 ≤ CurrentBudget.boundaryCost G d v - (CurrentRounding.hits G a I v : ℝ) := by
    by_cases hfull : CurrentBudget.boundaryCost G d v = (d + 1 : ℕ)
    · have hnot : ¬ 2 * a + 1 ≤ (CurrentRounding.hits G a I v : ℝ) := by
        intro h
        exact hnH (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvC, hnW⟩, h⟩)
      have hsmall : CurrentRounding.hits G a I v < d + 1 := by
        have hr : (CurrentRounding.hits G a I v : ℝ) < (d + 1 : ℕ) := by
          rw [hb]
          exact lt_of_not_ge hnot
        exact_mod_cast hr
      have hsmallR : (CurrentRounding.hits G a I v : ℝ) ≤ d := by exact_mod_cast (by omega : CurrentRounding.hits G a I v ≤ d)
      rw [hfull]
      push_cast
      linarith
    · have hcheap := CurrentBudget.cheap_closed_card G d hvC (lt_of_le_of_ne hc hfull)
      have hsub : closed G v ∩ CurrentRounding.residual G a I ⊆
          closed G v ∩ CurrentBudget.demands G d :=
        Finset.inter_subset_inter_left (CurrentRounding.residual_subset G a I)
      have hsmall : (CurrentRounding.hits G a I v : ℝ) ≤
          ((closed G v ∩ CurrentBudget.demands G d).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith
  refine ⟨?_, hgap⟩
  have hr : (CurrentRounding.hits G a I v : ℝ) ≤ d := by
    push_cast at hc
    linarith
  exact_mod_cast hr

theorem last_le_slack :
    ((CurrentRounding.last G a I).card : ℝ) ≤ d * CurrentRounding.slack G a I := by
  have hl := CurrentRounding.leftover_bound G a I
  refine hl.trans ?_
  unfold CurrentRounding.slack
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨hh, hgap⟩ := other_slack G a d hd x hx hcap v hv
  have hhR : (CurrentRounding.hits G a I v : ℝ) ≤ d := by exact_mod_cast hh
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcoef : (CurrentRounding.hits G a I v : ℝ) ≤
      d * (CurrentBudget.boundaryCost G d v - (CurrentRounding.hits G a I v : ℝ)) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoef (hx.1 v)
  simpa only [mul_assoc] using hm

theorem outside_le_middle (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a) :
    (CurrentRounding.outside G a I).card ≤ (CurrentRounding.middle G a I).card := by
  have he : 0 ≤ CurrentRounding.excess G a I := by
    apply Finset.sum_nonneg
    intro v hv
    exact sub_nonneg.mpr (Finset.mem_filter.mp hv).2
  have hh := CurrentRounding.excess_le G a I hden
  have hz : (0 : ℝ) ≤ (CurrentRounding.outside G a I).card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (CurrentRounding.middle G a I).card := Nat.cast_nonneg _
  have hreal : ((CurrentRounding.outside G a I).card : ℝ) ≤
      (CurrentRounding.middle G a I).card := by
    by_contra hn
    have hgt := lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_left hgt (by linarith : 0 < a + 1)
    nlinarith
  exact_mod_cast hreal

/-- Every current selected residual demand has at least d residual neighbors. -/
theorem overlap_degree {q : V} (hq : q ∈ CurrentRounding.overlap G a I) :
    d ≤ ((CurrentRounding.residual G a I).filter (G.Adj q)).card := by
  classical
  have hqH := (Finset.mem_inter.mp hq).1
  have hqR := (Finset.mem_inter.mp hq).2
  have hh : (d + 1 : ℕ) ≤ CurrentRounding.hits G a I q := by
    have hr := (Finset.mem_filter.mp hqH).2
    have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
    rw [← hb] at hr
    exact_mod_cast hr
  have he := Incidence.closed_inter_card G q (CurrentRounding.residual G a I)
  rw [if_pos hqR] at he
  change (closed G q ∩ CurrentRounding.residual G a I).card = _ at he
  unfold CurrentRounding.hits at hh
  omega

theorem overlap_neighbor_support {q v : V} (hq : q ∈ CurrentRounding.overlap G a I)
    (hv : v ∈ CurrentRounding.residual G a I) (ha : G.Adj q v) :
    v ∈ CurrentRounding.overlap G a I ∪ CurrentRounding.middle G a I := by
  classical
  by_cases hvH : v ∈ CurrentRounding.high G a I
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvH, hv⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨hv, Finset.mem_biUnion.mpr
        ⟨q, (Finset.mem_inter.mp hq).1, (mem_closed G v q).mpr (Or.inr ha)⟩⟩, hvH⟩)

/-- For a regular q in the current Q, every original neighbor is retained
in R. This is the non-contraction half of the final charging step. -/
theorem regular_overlap_neighbors {q : V} (hq : q ∈ CurrentRounding.overlap G a I)
    (hregular : G.degree q = d) :
    ∀ v, G.Adj q v → v ∈ CurrentRounding.residual G a I := by
  classical
  have hlow := overlap_degree G a d hd x hx hcap hq
  have hsub : (CurrentRounding.residual G a I).filter (G.Adj q) ⊆ G.neighborFinset q := by
    intro v hv
    exact (G.mem_neighborFinset q v).mpr (Finset.mem_filter.mp hv).2
  have he : (CurrentRounding.residual G a I).filter (G.Adj q) = G.neighborFinset q := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [SimpleGraph.card_neighborFinset_eq_degree, hregular] using hlow
  intro v hv
  have hm : v ∈ (CurrentRounding.residual G a I).filter (G.Adj q) := by
    rw [he]
    exact (G.mem_neighborFinset q v).mpr hv
  exact (Finset.mem_filter.mp hm).1

/-- The actual current Q\B vertices have defect neighbors in (B∩Q)∪L.
This uses F = V\N[B], and therefore does not reuse the old radius-two claim. -/
theorem regular_overlap_touches_defect {q : V}
    (hq : q ∈ CurrentRounding.overlap G a I) (hregular : G.degree q = d) :
    ∃ v ∈ (WeightedBudget.defects G d ∩ CurrentRounding.overlap G a I) ∪
      CurrentRounding.middle G a I, G.Adj q v := by
  classical
  have hqC : q ∈ CurrentBudget.candidates G d :=
    CurrentRounding.high_subset G a I (Finset.mem_inter.mp hq).1
  obtain ⟨v, hvB, hqv⟩ := Finset.mem_biUnion.mp hqC
  have hvne : q ≠ v := by
    intro heq
    subst v
    exact (Finset.mem_filter.mp hvB).2 hregular
  have ha : G.Adj q v := (((mem_closed G q v).mp hqv).resolve_left hvne).symm
  have hvR := regular_overlap_neighbors G a d hd x hx hcap hq hregular v ha
  have hs := overlap_neighbor_support G a d hd x hx hcap hq hvR ha
  rcases Finset.mem_union.mp hs with hvQ | hvL
  · exact ⟨v, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvB, hvQ⟩), ha⟩
  · exact ⟨v, Finset.mem_union_right _ hvL, ha⟩

end Paper.CurrentCounting
