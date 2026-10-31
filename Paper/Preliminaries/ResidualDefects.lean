import Paper.Endpoints.Rounding.SelectionGeometry
import Paper.Preliminaries.StarMinor
import Paper.Preliminaries.RadiusTwo

/-! Actual residual defects and radius-two coverage.
No minor density is assumed by the path argument. -/
namespace Paper.ResidualDefects
open SevenFoundation
open WeightedBudget (zone defects)
open SelectionGeometry
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Equality of induced and original degree forces retention of all neighbors. -/
theorem neighbors_retained (R : Finset V) (v : (R : Set V))
    (heq : (G.induce (R : Set V)).degree v = G.degree v.val) :
    ∀ u, G.Adj v.val u → u ∈ R := by
  have hmap := G.map_neighborFinset_induce (s := (R : Set V)) v
  have hcard : (G.neighborFinset v.val ∩ R).card = (G.neighborFinset v.val).card := by
    have hc := congrArg Finset.card hmap
    simp only [Finset.card_map, Finset.toFinset_coe,
      SimpleGraph.card_neighborFinset_eq_degree] at hc
    apply hc.symm.trans
    convert heq using 1 <;> congr 1
    exact Subsingleton.elim _ _
  have hset : G.neighborFinset v.val ∩ R = G.neighborFinset v.val :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (Nat.le_of_eq hcard.symm)
  intro u hu
  have hmem : u ∈ G.neighborFinset v.val ∩ R := by
    rw [hset]
    exact (G.mem_neighborFinset v.val u).mpr hu
  exact (Finset.mem_inter.mp hmem).2

noncomputable def localDefects (R : Finset V) (d : ℕ) : Finset (R : Set V) := by
  classical
  exact Finset.univ.filter (fun v => (G.induce (R : Set V)).degree v ≠ d ∨ G.degree v.val ≠ d)

theorem outside_localDefects (R : Finset V) (d : ℕ) {v : (R : Set V)}
    (hv : v ∉ localDefects G R d) :
    (G.induce (R : Set V)).degree v = d ∧ G.degree v.val = d := by
  classical
  simpa only [localDefects, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] using hv

/-- Stop just before the first exit of an original path of length at most two.
Equal degrees outside localDefects prevent such an exit at a regular vertex. -/
theorem localDefects_cover (R : Finset V) (d : ℕ) (hR : R ⊆ zone G d) :
    ∀ v, v ∈ covered (G.induce (R : Set V))
      (covered (G.induce (R : Set V)) (localDefects G R d)) := by
  classical
  intro v
  let J := G.induce (R : Set V)
  let S := localDefects G R d
  by_cases hv : v ∈ S
  · exact subset_covered J _ (subset_covered J _ hv)
  have hdeg := outside_localDefects G R d hv
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (hR v.property)
  have huR : u ∈ R := by
    rcases (mem_closed G v.val u).mp hvu with he | ha
    · exact he ▸ v.property
    · exact neighbors_retained G R v (hdeg.1.trans hdeg.2.symm) u ha.symm
  let uR : (R : Set V) := ⟨u, huR⟩
  have hclosed : v ∈ closed J uR := by
    apply (mem_closed J v uR).mpr
    rcases (mem_closed G v.val u).mp hvu with he | ha
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ha
  by_cases huS : uR ∈ S
  · exact Finset.mem_biUnion.mpr ⟨uR, subset_covered J S huS, hclosed⟩
  have huDeg := outside_localDefects G R d huS
  obtain ⟨b, hb, hub⟩ := Finset.mem_biUnion.mp hu
  have hbR : b ∈ R := by
    rcases (mem_closed G u b).mp hub with he | ha
    · exact he ▸ huR
    · exact neighbors_retained G R uR (huDeg.1.trans huDeg.2.symm) b ha.symm
  let bR : (R : Set V) := ⟨b, hbR⟩
  have hbS : bR ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inr ?_⟩
    exact (Finset.mem_filter.mp hb).2
  have hub' : uR ∈ closed J bR := by
    apply (mem_closed J uR bR).mpr
    rcases (mem_closed G u b).mp hub with he | ha
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ha
  exact Finset.mem_biUnion.mpr ⟨uR, Finset.mem_biUnion.mpr ⟨bR, hbS, hub'⟩, hclosed⟩

theorem residual_disjoint_covered (d : ℕ) (t : ℝ) (x : V → ℝ) :
    Disjoint (residual G d t x) (covered G (first G d t x)) := by
  classical
  exact Finset.disjoint_left.mpr (fun v hv hc => (Finset.mem_sdiff.mp hv).2 hc)

theorem actual_minor (d : ℕ) (t : ℝ) (x : V → ℝ) :
    SimpleGraph.IsMinor (StarMinor.graph G (first G d t x) (residual G d t x)) G :=
  StarMinor.isMinor G _ _ (residual_disjoint_covered G d t x)

/-- The actual residual region satisfies the sharp radius-two cardinality bound. -/
theorem residual_card_le (d : ℕ) (t : ℝ) (x : V → ℝ) (hd : 1 ≤ d)
    (hden : 2 * (G.induce (residual G d t x : Set V)).edgeFinset.card ≤
      d * (residual G d t x).card) :
    (residual G d t x).card ≤
      (1 + d ^ 2) * (localDefects G (residual G d t x) d).card := by
  classical
  let R := residual G d t x
  have hcard : Fintype.card (R : Set V) = R.card := Fintype.card_coe R
  have h := RadiusTwo.card_le (G.induce (R : Set V)) (localDefects G R d) d hd
    (fun v hv => (outside_localDefects G R d hv).1)
    (localDefects_cover G R d (residual_subset_zone G d t x))
  rw [hcard] at h
  exact h hden
end Paper.ResidualDefects
