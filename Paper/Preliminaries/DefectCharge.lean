import Paper.Preliminaries.StarCounting
import Paper.Preliminaries.ResidualDefects
import Paper.Endpoints.Rounding.SelectionSaving

/-! Charge original degree defects to actual edges of the star minor. -/
namespace Paper.DefectCharge
attribute [local instance] Classical.propDecidable
open SevenFoundation
open WeightedBudget (defects initialDemands)
open SelectionGeometry SelectionSaving
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (t : ℝ) (x : V → ℝ)

/-- A vertex of Q has at least d actual neighbors in R. -/
theorem overlap_degree {q : V} (hq : q ∈ overlap G d t x) :
    d ≤ ((residual G d t x).filter (G.Adj q)).card := by
  have hqH := (Finset.mem_inter.mp hq).1
  have hqR := (Finset.mem_inter.mp hq).2
  have hh : d + 1 ≤ hits G d t x q := (Finset.mem_filter.mp hqH).2
  have he := Incidence.closed_inter_card G q (residual G d t x)
  rw [if_pos hqR] at he
  change (closed G q ∩ residual G d t x).card = _ at he
  unfold hits at hh
  omega

theorem overlap_neighbor_support {q v : V} (hq : q ∈ overlap G d t x)
    (hv : v ∈ residual G d t x) (ha : G.Adj q v) :
    v ∈ overlap G d t x ∪ middle G d t x := by
  have hqH := (Finset.mem_inter.mp hq).1
  by_cases hvH : v ∈ high G d t x
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvH, hv⟩)
  · apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hv,
      Finset.mem_biUnion.mpr ⟨q, hqH, (mem_closed G v q).mpr (Or.inr ha)⟩⟩, hvH⟩

/-- A critical residual degree at an original defect forces an edge to N[W]. -/
theorem overlap_extra {q : V} (hq : q ∈ overlap G d t x)
    (hb : G.degree q ≠ d)
    (heq : ((residual G d t x).filter (G.Adj q)).card = d) :
    ∃ v ∈ covered G (first G d t x), G.Adj q v := by
  classical
  have hqB : q ∈ defects G d := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  have hex : ∃ v, G.Adj q v ∧ v ∉ residual G d t x := by
    by_contra hn
    push Not at hn
    have hs : (residual G d t x).filter (G.Adj q) = G.neighborFinset q := by
      ext v
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.2, fun ha => ⟨hn v ha, ha⟩⟩
    rw [hs, SimpleGraph.card_neighborFinset_eq_degree] at heq
    exact hb heq
  obtain ⟨v, ha, hvR⟩ := hex
  have hvnear : v ∈ covered G (defects G d) :=
    Finset.mem_biUnion.mpr ⟨q, hqB, (mem_closed G v q).mpr (Or.inr ha)⟩
  have hv0 := WeightedBudget.near_defect_subset_demands G d hvnear
  have hvW : v ∈ covered G (first G d t x) := by
    by_contra hn
    exact hvR (Finset.mem_sdiff.mpr ⟨hv0, hn⟩)
  exact ⟨v, hvW, ha⟩

set_option maxHeartbeats 2000000 in
/-- The graph-level inequality |B∩Q|≤t(w+ell), with an actual minor-density input. -/
theorem original_defects_le (hden : MinorDensity.Bound G t) (hd : (d : ℝ) = 2 * t) :
    ((defects G d ∩ overlap G d t x).card : ℝ) ≤
      t * ((first G d t x).card + (middle G d t x).card) := by
  classical
  let W := first G d t x
  let R := residual G d t x
  let Q := overlap G d t x
  let L := middle G d t x
  let C := W ∪ R
  let K := StarMinor.graph G W R
  let Q' := Q.subtype (fun v => v ∈ C)
  let X' := (L ∪ W).subtype (fun v => v ∈ C)
  let B' := (defects G d ∩ Q).subtype (fun v => v ∈ C)
  have hR := ResidualDefects.residual_disjoint_covered G d t x
  have hQC : Q ⊆ C := fun v hv => Finset.mem_union_right W (Finset.mem_inter.mp hv).2
  have hLC : L ⊆ C := fun v hv => Finset.mem_union_right W
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
  have hXC : L ∪ W ⊆ C := by
    intro v hv
    rcases Finset.mem_union.mp hv with hl | hw
    · exact hLC hl
    · exact Finset.mem_union_left R hw
  have hdis : Disjoint Q' X' := by
    apply Finset.disjoint_left.mpr
    intro q hq hx
    have hqQ := Finset.mem_subtype.mp hq
    rcases Finset.mem_union.mp (Finset.mem_subtype.mp hx) with hl | hw
    · exact (Finset.mem_sdiff.mp hl).2 (Finset.mem_inter.mp hqQ).1
    · exact Finset.disjoint_left.mp hR (Finset.mem_inter.mp hqQ).2 (subset_covered G W hw)
  have hB : B' ⊆ Q' := by
    intro q hq
    exact Finset.mem_subtype.mpr (Finset.mem_inter.mp (Finset.mem_subtype.mp hq)).2
  have hlower : ∀ q ∈ Q',
      d + (if q ∈ B' then 1 else 0) ≤ ((Q' ∪ X').filter (K.Adj q)).card := by
    intro q hq
    have hqQ : q.val ∈ Q := Finset.mem_subtype.mp hq
    have hqR : q.val ∈ R := (Finset.mem_inter.mp hqQ).2
    have h := StarCounting.degree_lower G W R (Q ∪ L) hR q hqR d
      (overlap_degree G d t x hqQ)
      (fun v hv ha => overlap_neighbor_support G d t x hqQ hv ha)
      (fun hb heq => overlap_extra G d t x hqQ hb heq)
    have hsets : (Q ∪ L ∪ W).subtype (fun v => v ∈ C) = Q' ∪ X' := by
      ext v
      simp only [Q', X', Finset.mem_subtype, Finset.mem_union]
      tauto
    have hbiff : q ∈ B' ↔ G.degree q.val ≠ d := by
      simp only [B', Finset.mem_subtype, Finset.mem_inter, WeightedBudget.defects, Finset.mem_filter,
        Finset.mem_univ, true_and, and_iff_left hqQ]
    change d + (if G.degree q.val ≠ d then 1 else 0) ≤
      (((Q ∪ L ∪ W).subtype (fun v => v ∈ C)).filter (K.Adj q)).card at h
    rw [hsets] at h
    simpa only [hbiff] using h
  have hkd := MinorDensity.minor_induced_bound G K hden (StarMinor.isMinor G W R hR)
  have hb := MinorDensity.charged_card_le K hkd d hd Q' X' B' hdis hB hlower
  have hbc : B'.card = (defects G d ∩ Q).card :=
    StarCounting.subtype_card C _ (fun v hv => hQC (Finset.mem_inter.mp hv).2)
  have hxc : X'.card = L.card + W.card := by
    rw [StarCounting.subtype_card C _ hXC]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp hR (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
      (subset_covered G W hw)
  rw [hbc, hxc] at hb
  push_cast at hb
  simpa only [add_comm] using hb
end Paper.DefectCharge
