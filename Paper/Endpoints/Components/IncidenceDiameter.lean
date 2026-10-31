import GraphTheory.DominationDiameter
import Paper.Endpoints.Components.IncidenceGraph
import Paper.Preliminaries.ShortChains

/-! Diameter bounds for actual covering-incidence components. Positive cover
costs bound the number of centers. The radius-one and radius-two diameter
arguments themselves are imported from `DominationDiameter`.
No physical-network simulation or exact cover search is asserted here. -/
namespace Paper.CoveringIncidence
open scoped BigOperators
variable {V : Type} [DecidableEq V]
variable (C : V → Finset V) (R : Finset V)

theorem component_neighbor (X : (graph C R).ConnectedComponent)
    (htwo : ∃ x y : X, x ≠ y) (v : X) :
    ∃ w : X, X.toSimpleGraph.Adj v w := by
  classical
  obtain ⟨x, y, hxy⟩ := htwo
  have hex : ∃ w : X, v ≠ w := by
    by_cases hv : v = x
    · exact ⟨y, hv ▸ hxy⟩
    · exact ⟨x, hv⟩
  obtain ⟨w, hvw⟩ := hex
  obtain ⟨p⟩ := X.connected_toSimpleGraph v w
  cases p with
  | nil => exact False.elim (hvw rfl)
  | cons ha p => exact ⟨_, ha⟩

/-- A nontrivial incidence component has no nondemand vertex without a demand
neighbor. This follows from the actual incidence relation, not an extra premise. -/
theorem nondemand_neighbor (X : (graph C R).ConnectedComponent)
    (htwo : ∃ x y : X, x ≠ y) (v : X) (hv : v.val ∉ R) :
    ∃ r : X, r.val ∈ R ∧ X.toSimpleGraph.Adj v r := by
  obtain ⟨r, ha⟩ := component_neighbor C R X htwo v
  have hi : (graph C R).Adj v.val r.val := ha
  rcases hi.2 with h | h
  · exact False.elim (hv h.1)
  · exact ⟨r, h.1, ha⟩

noncomputable def componentCenters (X : (graph C R).ConnectedComponent)
    (D : Finset V) : Finset X := by
  classical
  exact D.subtype (fun v => v ∈ X.supp)

omit [DecidableEq V] in
theorem mem_componentCenters (X : (graph C R).ConnectedComponent)
    (D : Finset V) (d : X) : d ∈ componentCenters C R X D ↔ d.val ∈ D := by
  classical
  exact Finset.mem_subtype

omit [DecidableEq V] in
theorem componentCenters_card_le (X : (graph C R).ConnectedComponent) (D : Finset V) :
    (componentCenters C R X D).card ≤ D.card := by
  classical
  rw [componentCenters, Finset.card_subtype]
  exact Finset.card_filter_le _ _

/-- A demanded row is covered by a center in its own component. -/
theorem demand_center (X : (graph C R).ConnectedComponent) (D : Finset V)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r)
    (r : X) (hr : r.val ∈ R) :
    ∃ d ∈ componentCenters C R X D, r = d ∨ X.toSimpleGraph.Adj r d := by
  obtain ⟨d, hd, hdr⟩ := hcover r.val hr r.property
  have hnear := candidate_self_or_adj C R hr hdr
  have hdX : d ∈ X.supp := by
    rcases hnear with he | ha
    · simpa only [he] using r.property
    · exact X.mem_supp_of_adj_mem_supp r.property ha
  refine ⟨⟨d, hdX⟩, (mem_componentCenters C R X D _).mpr hd, ?_⟩
  rcases hnear with he | ha
  · exact Or.inl (Subtype.ext he.symm)
  · exact Or.inr ha

theorem component_radius_two (X : (graph C R).ConnectedComponent) (D : Finset V)
    (htwo : ∃ x y : X, x ≠ y)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r) (v : X) :
    ∃ d ∈ componentCenters C R X D, X.toSimpleGraph.dist v d ≤ 2 := by
  classical
  have hex : ∃ r : X, r.val ∈ R ∧ (v = r ∨ X.toSimpleGraph.Adj v r) := by
    by_cases hv : v.val ∈ R
    · exact ⟨v, hv, Or.inl rfl⟩
    · obtain ⟨r, hr, ha⟩ := nondemand_neighbor C R X htwo v hv
      exact ⟨r, hr, Or.inr ha⟩
  obtain ⟨r, hr, hvr⟩ := hex
  obtain ⟨d, hd, hrd⟩ := demand_center C R X D hcover r hr
  obtain ⟨p, hp, _⟩ := ShortChains.chain3 X.toSimpleGraph v r d hvr hrd
  exact ⟨d, hd, (SimpleGraph.dist_le p).trans hp⟩

theorem component_radius_one (X : (graph C R).ConnectedComponent) (D : Finset V)
    (hall : ∀ r ∈ X.supp, r ∈ R)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r) (v : X) :
    ∃ d ∈ componentCenters C R X D, X.toSimpleGraph.dist v d ≤ 1 := by
  obtain ⟨d, hd, hnear⟩ := demand_center C R X D hcover v (hall v.val v.property)
  obtain ⟨p, hp, _⟩ := ShortChains.step X.toSimpleGraph hnear
  exact ⟨d, hd, (SimpleGraph.dist_le p).trans hp⟩

omit [DecidableEq V] in
theorem card_le_cost (D : Finset V) (c : V → ℝ) (K : ℕ)
    (hc : ∀ d ∈ D, 1 ≤ c d) (hcost : (∑ d ∈ D, c d) ≤ (K : ℝ)) : D.card ≤ K := by
  have hcard : (D.card : ℝ) ≤ (K : ℝ) := calc
    (D.card : ℝ) = ∑ _d ∈ D, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ D, c d := Finset.sum_le_sum hc
    _ ≤ (K : ℝ) := hcost
  exact_mod_cast hcard

/-- The singleton case includes an isolated nondemand with an empty cover.
No nonisolation assumption is imposed on the final component theorem. -/
theorem component_distance_le_five (X : (graph C R).ConnectedComponent)
    (D : Finset V) (c : V → ℝ) (K : ℕ) (_hK : 1 ≤ K)
    (hc : ∀ d ∈ D, 1 ≤ c d) (hcost : (∑ d ∈ D, c d) ≤ (K : ℝ))
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r) (x y : X) :
    X.toSimpleGraph.dist x y ≤ 5 * K - 1 := by
  classical
  by_cases htwo : ∃ u w : X, u ≠ w
  · exact SimpleGraph.DominationDiameter.radius_two_distance_le X.toSimpleGraph
      X.connected_toSimpleGraph (componentCenters C R X D) K
      (component_radius_two C R X D htwo hcover)
      ((componentCenters_card_le C R X D).trans (card_le_cost D c K hc hcost)) x y
  · have he : x = y := by by_contra h; exact htwo ⟨x, y, h⟩
    subst y
    rw [SimpleGraph.dist_self]
    omega

theorem component_distance_le_three (X : (graph C R).ConnectedComponent)
    (D : Finset V) (c : V → ℝ) (K : ℕ) (_hK : 1 ≤ K)
    (hc : ∀ d ∈ D, 1 ≤ c d) (hcost : (∑ d ∈ D, c d) ≤ (K : ℝ))
    (hall : ∀ r ∈ X.supp, r ∈ R)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r) (x y : X) :
    X.toSimpleGraph.dist x y ≤ 3 * K - 1 := by
  have hcard := (componentCenters_card_le C R X D).trans (card_le_cost D c K hc hcost)
  have h := SimpleGraph.DominationDiameter.radius_one_distance_le X.toSimpleGraph
    X.connected_toSimpleGraph (componentCenters C R X D) K
    (component_radius_one C R X D hall hcover) hcard x y
  omega

omit [DecidableEq V] in
/-- An isolated nondemand is a singleton instance component, admits the empty
cover, and has diameter zero. -/
theorem isolated_nondemand (v : V) (hv : v ∉ R)
    (hiso : ∀ w, ¬ (graph C R).Adj v w) :
    let X := (graph C R).connectedComponentMk v
    X.supp = {v} ∧
      (∀ r ∈ R, r ∈ X.supp → ∃ d ∈ (∅ : Finset V), d ∈ C r) ∧
      ∀ x y : X, X.toSimpleGraph.dist x y = 0 := by
  classical
  dsimp only
  let X := (graph C R).connectedComponentMk v
  have he : ∀ w ∈ X.supp, w = v := by
    intro w hw
    obtain ⟨p⟩ := X.reachable_of_mem_supp (by rfl) hw
    cases p with
    | nil => rfl
    | cons ha p => exact False.elim (hiso _ ha)
  refine ⟨?_, ?_, ?_⟩
  · ext w
    constructor
    · intro hw; exact Set.mem_singleton_iff.mpr (he w hw)
    · intro hw; obtain rfl := Set.mem_singleton_iff.mp hw; rfl
  · intro r hr hrX
    exact False.elim (hv ((he r hrX) ▸ hr))
  · intro x y
    have hxy : x = y := Subtype.ext ((he x.val x.property).trans (he y.val y.property).symm)
    subst y
    exact SimpleGraph.dist_self

/-- Project the component distance guarantee to a genuine ambient incidence walk. -/
theorem component_walk_le_five (X : (graph C R).ConnectedComponent)
    (D : Finset V) (c : V → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hc : ∀ d ∈ D, 1 ≤ c d) (hcost : (∑ d ∈ D, c d) ≤ (K : ℝ))
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r)
    {u v : V} (hu : u ∈ X.supp) (hv : v ∈ X.supp) :
    ∃ p : (graph C R).Walk u v, p.length ≤ 5 * K - 1 := by
  obtain ⟨p, hp⟩ := X.connected_toSimpleGraph.exists_walk_length_eq_dist ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨p.map X.toSimpleGraph_hom, ?_⟩
  have hlen := SimpleGraph.Walk.length_map X.toSimpleGraph_hom p
  exact hlen.le.trans (hp.le.trans
    (component_distance_le_five C R X D c K hK hc hcost hcover _ _))

theorem component_walk_le_three (X : (graph C R).ConnectedComponent)
    (D : Finset V) (c : V → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hc : ∀ d ∈ D, 1 ≤ c d) (hcost : (∑ d ∈ D, c d) ≤ (K : ℝ))
    (hall : ∀ r ∈ X.supp, r ∈ R)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ C r)
    {u v : V} (hu : u ∈ X.supp) (hv : v ∈ X.supp) :
    ∃ p : (graph C R).Walk u v, p.length ≤ 3 * K - 1 := by
  obtain ⟨p, hp⟩ := X.connected_toSimpleGraph.exists_walk_length_eq_dist ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨p.map X.toSimpleGraph_hom, ?_⟩
  have hlen := SimpleGraph.Walk.length_map X.toSimpleGraph_hom p
  exact hlen.le.trans (hp.le.trans
    (component_distance_le_three C R X D c K hK hc hcost hall hcover _ _))

end Paper.CoveringIncidence

#print axioms Paper.CoveringIncidence.nondemand_neighbor
#print axioms Paper.CoveringIncidence.component_distance_le_five
#print axioms Paper.CoveringIncidence.component_distance_le_three
#print axioms Paper.CoveringIncidence.isolated_nondemand
#print axioms Paper.CoveringIncidence.component_walk_le_five
#print axioms Paper.CoveringIncidence.component_walk_le_three
