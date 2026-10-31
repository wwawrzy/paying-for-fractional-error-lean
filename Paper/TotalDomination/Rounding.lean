import Paper.Preliminaries.Incidence
import Paper.Endpoints.Rounding.GeneralCoveringRounding

/-! The open-neighborhood selection in `fv:total:rule`, with its coverage,
cardinality bound and density saving from `fv:total:rounding`. The cost
inequality and the final exact approximation coefficient are not proved here. -/

namespace Paper.TotalDomination

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Input where
  candidates : Finset V
  demands : Finset V
  eligible : Finset V
  eligible_subset : eligible ⊆ candidates
  x : V → ℝ
  threshold : ℝ
  cutoff : ℕ
  identifier : V → ℕ
  isolate_free : ∀ r, (G.neighborFinset r).Nonempty

variable (I : Input G)

/-- Open neighborhoods only: a selected vertex need not cover itself. -/
def neighbors (S : Finset V) : Finset V := S.biUnion (fun v => G.neighborFinset v)

theorem mem_neighbors {S : Finset V} {r : V} :
    r ∈ neighbors G S ↔ ∃ v ∈ S, G.Adj r v := by
  simp only [neighbors, Finset.mem_biUnion, SimpleGraph.mem_neighborFinset]
  exact exists_congr fun v => and_congr_right fun _ => G.adj_comm v r

theorem neighbors_mono {S T : Finset V} (h : S ⊆ T) :
    neighbors G S ⊆ neighbors G T := by
  intro r hr
  obtain ⟨v, hv, hadj⟩ := (mem_neighbors G).mp hr
  exact (mem_neighbors G).mpr ⟨v, h hv, hadj⟩

noncomputable def first : Finset V := by
  classical
  exact I.eligible.filter (fun v => I.threshold < I.x v)

noncomputable def residual : Finset V := I.demands \ neighbors G (first G I)

noncomputable def hits (v : V) : ℕ := (G.neighborFinset v ∩ residual G I).card

noncomputable def high : Finset V := by
  classical
  exact (I.candidates \ first G I).filter (fun v => I.cutoff ≤ hits G I v)

noncomputable def served : Finset V := residual G I ∩ neighbors G (high G I)

noncomputable def last : Finset V := residual G I \ served G I

noncomputable def request (r : V) : V :=
  GeneralCoveringRounding.cheapest (fun v => G.neighborFinset v)
    (fun v => (I.identifier v : ℝ)) r (I.isolate_free r)

noncomputable def output : Finset V :=
  first G I ∪ high G I ∪ (last G I).image (request G I)

noncomputable def surplus : ℝ := (served G I).card - (high G I).card

noncomputable def excess (a : ℝ) : ℝ :=
  ∑ v ∈ high G I, ((hits G I v : ℝ) - 2 * a)

theorem request_adj (r : V) : G.Adj r (request G I r) := by
  exact (G.mem_neighborFinset r _).mp
    (GeneralCoveringRounding.cheapest_mem (fun v => G.neighborFinset v)
      (fun v => (I.identifier v : ℝ)) r (I.isolate_free r))

theorem request_identifier_le (r v : V) (h : G.Adj r v) :
    I.identifier (request G I r) ≤ I.identifier v := by
  have hh := GeneralCoveringRounding.cheapest_cost_le (fun v => G.neighborFinset v)
    (fun v => (I.identifier v : ℝ)) r v (I.isolate_free r)
    ((G.mem_neighborFinset r v).mpr h)
  change (I.identifier (request G I r) : ℝ) ≤ (I.identifier v : ℝ) at hh
  exact_mod_cast hh

/-- Each demand has an actual adjacent selected vertex, including demands
that were themselves selected during the first step. -/
theorem output_covers : ∀ r ∈ I.demands, ∃ v ∈ output G I, G.Adj r v := by
  classical
  intro r hr
  by_cases hw : r ∈ neighbors G (first G I)
  · obtain ⟨v, hv, hadj⟩ := (mem_neighbors G).mp hw
    exact ⟨v, Finset.mem_union_left _ (Finset.mem_union_left _ hv), hadj⟩
  have hR : r ∈ residual G I := Finset.mem_sdiff.mpr ⟨hr, hw⟩
  by_cases hh : r ∈ neighbors G (high G I)
  · obtain ⟨v, hv, hadj⟩ := (mem_neighbors G).mp hh
    exact ⟨v, Finset.mem_union_left _ (Finset.mem_union_right _ hv), hadj⟩
  have hu : r ∈ last G I :=
    Finset.mem_sdiff.mpr ⟨hR, fun hy => hh (Finset.mem_inter.mp hy).2⟩
  exact ⟨request G I r, Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨r, hu, rfl⟩), request_adj G I r⟩

/-- The total domination conclusion, when every vertex is a demand. -/
theorem output_total_dominates (h : I.demands = Finset.univ) :
    ∀ r, ∃ v ∈ output G I, G.Adj r v := by
  intro r
  apply output_covers G I r
  simp [h]

theorem output_card_le :
    ((output G I).card : ℝ) ≤
      (first G I).card + (residual G I).card - surplus G I := by
  have hcard := Finset.card_union_le (first G I ∪ high G I)
    ((last G I).image (request G I))
  have hfirst := Finset.card_union_le (first G I) (high G I)
  have himage := Finset.card_image_le (s := last G I) (f := request G I)
  have hsplit := Finset.card_sdiff_add_card_inter (residual G I) (served G I)
  have hserved : residual G I ∩ served G I = served G I :=
    Finset.inter_eq_right.mpr Finset.inter_subset_left
  rw [hserved] at hsplit
  have hn : (output G I).card + (served G I).card ≤
      (first G I).card + (high G I).card + (residual G I).card := by
    change (last G I).card + (served G I).card = (residual G I).card at hsplit
    change (output G I).card ≤ _ at hcard
    omega
  have hr : ((output G I).card : ℝ) + (served G I).card ≤
      (first G I).card + (high G I).card + (residual G I).card := by exact_mod_cast hn
  unfold surplus
  linarith

/-- All incidences from H to R have their demand endpoint in Y. -/
theorem high_incidence_eq :
    (G.interedges (high G I) (served G I)).card =
      ∑ v ∈ high G I, hits G I v := by
  classical
  rw [Incidence.card_interedges_eq_sum]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext r
  simp only [Finset.mem_filter, served, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hr, _⟩, ha⟩
    exact ⟨ha, hr⟩
  · rintro ⟨ha, hr⟩
    exact ⟨⟨hr, (mem_neighbors G).mpr ⟨v, hv, ha.symm⟩⟩, ha⟩

/-- Reuses the overlapping-set edge count, with no disjointness assumption
on H and Y. This is `fv:total:E`. -/
theorem excess_le (a : ℝ) (hdensity : Incidence.InducedDensityBound G a) :
    excess G I a ≤ a * surplus G I := by
  have hn := Incidence.card_interedges_le G (high G I) (served G I)
  rw [high_incidence_eq G I] at hn
  have hr : (∑ v ∈ high G I, (hits G I v : ℝ)) ≤
      (G.inducedEdgeCount (high G I ∪ served G I) : ℝ) +
      (G.inducedEdgeCount (high G I ∩ served G I) : ℝ) := by exact_mod_cast hn
  have hU := hdensity (high G I ∪ served G I)
  have hA := hdensity (high G I ∩ served G I)
  have hcard := Finset.card_union_add_card_inter (high G I) (served G I)
  have hcardR : ((high G I ∪ served G I).card : ℝ) +
      (high G I ∩ served G I).card = (high G I).card + (served G I).card :=
    by exact_mod_cast hcard
  have hweighted := congrArg (fun z : ℝ => a * z) hcardR
  have he : excess G I a = (∑ v ∈ high G I, (hits G I v : ℝ)) -
      (high G I).card * (2 * a) := by simp [excess, Finset.sum_sub_distrib]
  rw [he]
  unfold surplus
  nlinarith only [hr, hU, hA, hweighted]

theorem excess_nonneg (a : ℝ) (hcutoff : 2 * a ≤ I.cutoff) :
    0 ≤ excess G I a := by
  classical
  apply Finset.sum_nonneg
  intro v hv
  have h := (Finset.mem_filter.mp hv).2
  have hR : (I.cutoff : ℝ) ≤ hits G I v := by exact_mod_cast h
  linarith

theorem surplus_nonneg (a : ℝ) (ha : 0 < a)
    (hdensity : Incidence.InducedDensityBound G a) (hcutoff : 2 * a ≤ I.cutoff) :
    0 ≤ surplus G I := by
  have hE := excess_nonneg G I a hcutoff
  have hbound := excess_le G I a hdensity
  nlinarith

end Paper.TotalDomination

#print axioms Paper.TotalDomination.request_identifier_le
#print axioms Paper.TotalDomination.output_covers
#print axioms Paper.TotalDomination.output_total_dominates
#print axioms Paper.TotalDomination.output_card_le
#print axioms Paper.TotalDomination.excess_le
#print axioms Paper.TotalDomination.surplus_nonneg
