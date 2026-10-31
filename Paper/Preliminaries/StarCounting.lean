import Paper.Preliminaries.MinorDensity

/-! Degree charges survive simple star contraction, including one extra edge
for each original defect whose residual degree is exactly the critical degree. -/
namespace Paper.StarCounting
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem subtype_card (C A : Finset V) (h : A ⊆ C) :
    (A.subtype (fun v => v ∈ C)).card = A.card := by
  rw [Finset.card_subtype, Finset.filter_true_of_mem h]

theorem degree_lower (W R T : Finset V) (hR : Disjoint R (covered G W))
    (q : {v // v ∈ W ∪ R}) (hq : q.val ∈ R) (d : ℕ)
    (hdeg : d ≤ (R.filter (G.Adj q.val)).card)
    (hsupport : ∀ v ∈ R, G.Adj q.val v → v ∈ T)
    (hextra : G.degree q.val ≠ d → (R.filter (G.Adj q.val)).card = d →
      ∃ v ∈ covered G W, G.Adj q.val v) :
    d + (if G.degree q.val ≠ d then 1 else 0) ≤
      (((T ∪ W).subtype (fun v => v ∈ W ∪ R)).filter
        ((StarMinor.graph G W R).Adj q)).card := by
  classical
  let K := StarMinor.graph G W R
  let D := R.filter (G.Adj q.val)
  let D' := D.subtype (fun v => v ∈ W ∪ R)
  let N := ((T ∪ W).subtype (fun v => v ∈ W ∪ R)).filter (K.Adj q)
  have hc : D'.card = D.card := subtype_card (W ∪ R) D
    (fun v hv => Finset.mem_union_right W (Finset.mem_filter.mp hv).1)
  have hsub : D' ⊆ N := by
    intro v hv
    have hvD := Finset.mem_subtype.mp hv
    have hvR := (Finset.mem_filter.mp hvD).1
    have ha := (Finset.mem_filter.mp hvD).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_subtype.mpr (Finset.mem_union_left _ (hsupport v.val hvR ha)), ?_⟩
    exact StarMinor.residual_edge G W R hR hq hvR ha
  have hbase : D.card ≤ N.card := hc ▸ Finset.card_le_card hsub
  change d ≤ D.card at hdeg
  change d + (if G.degree q.val ≠ d then 1 else 0) ≤ N.card
  by_cases hb : G.degree q.val ≠ d
  · simp only [if_pos hb]
    by_cases hg : d < D.card
    · omega
    have heq : D.card = d := by omega
    obtain ⟨v, hv, ha⟩ := hextra hb heq
    obtain ⟨w, hw, hqw⟩ := StarMinor.boundary_edge G W R hR hq hv ha
    let wK : {v // v ∈ W ∪ R} := ⟨w, Finset.mem_union_left R hw⟩
    have hwN : wK ∈ N := Finset.mem_filter.mpr
      ⟨Finset.mem_subtype.mpr (Finset.mem_union_right T hw), hqw⟩
    have hwD : wK ∉ D' := by
      intro hwD
      have hwR := (Finset.mem_filter.mp (Finset.mem_subtype.mp hwD)).1
      exact Finset.disjoint_left.mp hR hwR (subset_covered G W hw)
    have hins : insert wK D' ⊆ N := Finset.insert_subset hwN hsub
    have hc' := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hwD, hc] at hc'
    omega
  · simp only [if_neg hb, add_zero]
    exact hdeg.trans hbase
end Paper.StarCounting
