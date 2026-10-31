import Paper.Preliminaries.ComponentMap
import Paper.Preliminaries.MinorDensity

/-!
Actual component contraction for the current endpoint count. Components of
G-R meeting W are contracted in their entirety; every other vertex remains
a singleton. R is always retained, without a star/radius assumption.

The model, residual edges, residual degree lower bounds, and degree equality
at untouched vertices are proved from the explicit labels below. The choice
of component roots is used only in the mathematical minor, not by the
distributed algorithm.
-/

namespace Paper.ComponentMinor

attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (R W : Finset V)

noncomputable def cluster (v : V) : Finset V :=
  ComponentMap.part G (Finset.univ \ R) v

noncomputable def marked (v : V) : Finset V := cluster G R v ∩ W

noncomputable def label (v : V) : V :=
  if h : (marked G R W v).Nonempty then h.choose else v

theorem cluster_subset (v : V) : cluster G R v ⊆ Finset.univ \ R :=
  ComponentMap.subset G _ v

theorem cluster_self {v : V} (hv : v ∉ R) : v ∈ cluster G R v :=
  ComponentMap.mem_self G _ v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩)

theorem cluster_nonempty_outside {v : V} (hv : (cluster G R v).Nonempty) : v ∉ R := by
  by_cases hs : v ∈ (Finset.univ : Finset V) \ R
  · exact (Finset.mem_sdiff.mp hs).2
  · simp only [cluster, ComponentMap.part, dif_neg hs] at hv
    exact False.elim (Finset.not_nonempty_empty hv)

theorem cluster_eq_of_mem {u v : V} (hu : u ∈ cluster G R v) :
    cluster G R u = cluster G R v := ComponentMap.eq_of_mem G _ u v hu

theorem marked_nonempty_outside {v : V} (hv : (marked G R W v).Nonempty) : v ∉ R := by
  obtain ⟨u, hu⟩ := hv
  exact cluster_nonempty_outside G R ⟨u, (Finset.mem_inter.mp hu).1⟩

theorem unmarked_of_mem {v : V} (hv : v ∈ R) : ¬ (marked G R W v).Nonempty := by
  intro h
  exact marked_nonempty_outside G R W h hv

theorem label_unmarked {v : V} (hv : ¬ (marked G R W v).Nonempty) : label G R W v = v :=
  dif_neg hv

theorem label_marked {v : V} (hv : (marked G R W v).Nonempty) :
    label G R W v ∈ marked G R W v := by
  simp only [label, dif_pos hv]
  exact hv.choose_spec

theorem label_eq_of_cluster_eq {u v : V} (he : cluster G R u = cluster G R v)
    (hv : (marked G R W v).Nonempty) : label G R W u = label G R W v := by
  have hm : marked G R W u = marked G R W v := congrArg (fun S => S ∩ W) he
  simp only [label, hm, dif_pos hv]

theorem label_idempotent (v : V) : label G R W (label G R W v) = label G R W v := by
  by_cases hv : (marked G R W v).Nonempty
  · exact label_eq_of_cluster_eq G R W
      (cluster_eq_of_mem G R (Finset.mem_inter.mp (label_marked G R W hv)).1) hv
  · rw [label_unmarked G R W hv]
    exact label_unmarked G R W hv

theorem label_residual {v : V} (hv : v ∈ R) : label G R W v = v :=
  label_unmarked G R W (unmarked_of_mem G R W hv)

theorem label_outside {v : V} (hv : v ∉ R) : label G R W v ∉ R := by
  by_cases hm : (marked G R W v).Nonempty
  · have hmem := (Finset.mem_inter.mp (label_marked G R W hm)).1
    exact (Finset.mem_sdiff.mp (cluster_subset G R v hmem)).2
  · rwa [label_unmarked G R W hm]

noncomputable def retained : Finset V := Finset.univ.image (label G R W)

theorem retained_fixed {v : V} (hv : v ∈ retained G R W) : label G R W v = v := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact label_idempotent G R W u

noncomputable def vertex (v : V) : retained G R W :=
  ⟨label G R W v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩

theorem fiber_marked (r : V) (hr : label G R W r = r)
    (hm : (marked G R W r).Nonempty) :
    {v | label G R W v = r} = (cluster G R r : Set V) := by
  ext v
  constructor
  · intro hv
    by_cases hvm : (marked G R W v).Nonempty
    · have hrC : r ∈ cluster G R v := by
        rw [← hv]
        exact (Finset.mem_inter.mp (label_marked G R W hvm)).1
      have he := cluster_eq_of_mem G R hrC
      rw [he]
      exact cluster_self G R (marked_nonempty_outside G R W hvm)
    · have he : v = r := (label_unmarked G R W hvm).symm.trans hv
      subst v
      exact cluster_self G R (marked_nonempty_outside G R W hm)
  · intro hv
    exact (label_eq_of_cluster_eq G R W (cluster_eq_of_mem G R hv) hm).trans hr

theorem fiber_unmarked (r : V) (hr : label G R W r = r)
    (hm : ¬ (marked G R W r).Nonempty) : {v | label G R W v = r} = {r} := by
  ext v
  constructor
  · intro hv
    by_cases hvm : (marked G R W v).Nonempty
    · have hrM : r ∈ marked G R W v := by
        rw [← hv]
        exact label_marked G R W hvm
      have he := cluster_eq_of_mem G R (Finset.mem_inter.mp hrM).1
      have hme : marked G R W r = marked G R W v := congrArg (fun S => S ∩ W) he
      exact False.elim (hm (hme.symm ▸ hvm))
    · exact (label_unmarked G R W hvm).symm.trans hv
  · intro hv
    change v = r at hv
    subst v
    exact hr

noncomputable def graph : SimpleGraph (retained G R W) where
  Adj r s := r ≠ s ∧ ∃ u v, label G R W u = r.val ∧ label G R W v = s.val ∧ G.Adj u v
  symm := by
    rintro r s ⟨hne, u, v, hu, hv, ha⟩
    exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Nonempty disjoint connected fibers form the actual component minor. -/
noncomputable def model : SimpleGraph.MinorModel (graph G R W) G where
  branchSet r := {v | label G R W v = r.val}
  nonempty r := ⟨r.val, retained_fixed G R W r.property⟩
  disjoint r s hne := by
    apply Set.disjoint_left.mpr
    intro v hv hs
    exact hne (Subtype.ext (hv.symm.trans hs))
  connected r := by
    have hr := retained_fixed G R W r.property
    by_cases hm : (marked G R W r.val).Nonempty
    · rw [fiber_marked G R W r.val hr hm]
      exact ComponentMap.connected G (Finset.univ \ R) r.val
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, marked_nonempty_outside G R W hm⟩)
    · rw [fiber_unmarked G R W r.val hr hm]
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨r.val, rfl⟩, ?_⟩
      intro v
      have he : (⟨r.val, rfl⟩ : {v // v ∈ ({r.val} : Set V)}) = v :=
        Subtype.ext v.property.symm
      rw [he]
  adjacent r s h := by
    obtain ⟨_, u, v, hu, hv, ha⟩ := h
    exact ⟨u, hu, v, hv, ha⟩

theorem isMinor : SimpleGraph.IsMinor (graph G R W) G := ⟨model G R W⟩

theorem edge_of_different_labels {u v : V} (ha : G.Adj u v)
    (hne : label G R W u ≠ label G R W v) :
    (graph G R W).Adj (vertex G R W u) (vertex G R W v) := by
  refine ⟨?_, u, v, rfl, rfl, ha⟩
  intro he
  exact hne (congrArg Subtype.val he)

/-- G[R] is retained with its original vertices and edges. -/
theorem residual_edge {u v : V} (hu : u ∈ R) (hv : v ∈ R) (ha : G.Adj u v) :
    (graph G R W).Adj (vertex G R W u) (vertex G R W v) := by
  apply edge_of_different_labels G R W ha
  rw [label_residual G R W hu, label_residual G R W hv]
  exact ha.ne

theorem label_eq_residual_iff {r v : V} (hr : r ∈ R) :
    label G R W v = r ↔ v = r := by
  change v ∈ {u | label G R W u = r} ↔ v ∈ ({r} : Set V)
  rw [fiber_unmarked G R W r (label_residual G R W hr) (unmarked_of_mem G R W hr)]

/-- Contraction neither deletes nor introduces an edge between residual
vertices: the induced graph on R is unchanged. -/
theorem residual_edge_iff {u v : V} (hu : u ∈ R) (hv : v ∈ R) :
    (graph G R W).Adj (vertex G R W u) (vertex G R W v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨_, p, q, hp, hq, hpq⟩
    change label G R W p = label G R W u at hp
    change label G R W q = label G R W v at hq
    rw [label_residual G R W hu] at hp
    rw [label_residual G R W hv] at hq
    have hpu := (label_eq_residual_iff G R W hu).mp hp
    have hqv := (label_eq_residual_iff G R W hv).mp hq
    subst p
    subst q
    exact hpq
  · exact residual_edge G R W hu hv

theorem residual_to_outside_edge {q v : V} (hq : q ∈ R) (hv : v ∉ R) (ha : G.Adj q v) :
    (graph G R W).Adj (vertex G R W q) (vertex G R W v) := by
  apply edge_of_different_labels G R W ha
  rw [label_residual G R W hq]
  intro he
  exact label_outside G R W hv (he ▸ hq)

/-- Residual neighbors remain distinct; an outside neighbor gives one
additional distinct neighbor even if its entire component is contracted. -/
theorem residual_degree_lower {q : V} (hq : q ∈ R) :
    (R.filter (G.Adj q)).card ≤ (graph G R W).degree (vertex G R W q) ∧
    (∀ v, v ∉ R → G.Adj q v →
      (R.filter (G.Adj q)).card + 1 ≤ (graph G R W).degree (vertex G R W q)) := by
  classical
  let D := R.filter (G.Adj q)
  have hinj : Set.InjOn (vertex G R W) (D : Set V) := by
    intro u hu v hv he
    have he' := congrArg Subtype.val he
    change label G R W u = label G R W v at he'
    rw [label_residual G R W (Finset.mem_filter.mp hu).1,
      label_residual G R W (Finset.mem_filter.mp hv).1] at he'
    exact he'
  have hcard : (D.image (vertex G R W)).card = D.card := Finset.card_image_of_injOn hinj
  have hsub : D.image (vertex G R W) ⊆ (graph G R W).neighborFinset (vertex G R W q) := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    exact ((graph G R W).mem_neighborFinset _ _).mpr
      (residual_edge G R W hq (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2)
  have hbase := Finset.card_le_card hsub
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree] at hbase
  refine ⟨hbase, ?_⟩
  intro v hvR hqv
  have hn : vertex G R W v ∉ D.image (vertex G R W) := by
    intro hm
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
    have he' := congrArg Subtype.val he
    change label G R W u = label G R W v at he'
    rw [label_residual G R W (Finset.mem_filter.mp hu).1] at he'
    exact label_outside G R W hvR (he' ▸ (Finset.mem_filter.mp hu).1)
  have hsub' : insert (vertex G R W v) (D.image (vertex G R W)) ⊆
      (graph G R W).neighborFinset (vertex G R W q) := by
    intro r hr
    rcases Finset.mem_insert.mp hr with he | hm
    · subst r
      exact ((graph G R W).mem_neighborFinset _ _).mpr
        (residual_to_outside_edge G R W hq hvR hqv)
    · exact hsub hm
  have hh := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem hn, hcard, SimpleGraph.card_neighborFinset_eq_degree] at hh
  exact hh

/-- An original defect with at least d residual neighbors has degree at
least d+1 after the actual contraction, even when extra edges merge. -/
theorem defect_residual_degree (d : ℕ) {q : V} (hq : q ∈ R)
    (hlow : d ≤ (R.filter (G.Adj q)).card) (hdef : G.degree q ≠ d) :
    d + 1 ≤ (graph G R W).degree (vertex G R W q) := by
  classical
  obtain ⟨hbase, hextra⟩ := residual_degree_lower G R W hq
  by_cases hgt : d < (R.filter (G.Adj q)).card
  · omega
  have heq : (R.filter (G.Adj q)).card = d := by omega
  have hout : ∃ v, v ∉ R ∧ G.Adj q v := by
    by_contra hn
    have hall : ∀ v, G.Adj q v → v ∈ R := by
      intro v ha
      by_contra hv
      exact hn ⟨v, hv, ha⟩
    have he : R.filter (G.Adj q) = G.neighborFinset q := by
      ext v
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨And.right, fun ha => ⟨hall v ha, ha⟩⟩
    rw [he, SimpleGraph.card_neighborFinset_eq_degree] at heq
    exact hdef heq
  obtain ⟨v, hv, ha⟩ := hout
  have hh := hextra v hv ha
  omega

theorem neighbor_fixed_of_uncontracted {v : V} (hvR : v ∉ R)
    (hvM : ¬ (marked G R W v).Nonempty) {u : V} (ha : G.Adj v u) :
    label G R W u = u := by
  by_cases huR : u ∈ R
  · exact label_residual G R W huR
  · have he : cluster G R u = cluster G R v :=
      ComponentMap.eq_of_adj G (Finset.univ \ R) u v
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huR⟩)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvR⟩) ha.symm
    have hm : marked G R W u = marked G R W v := congrArg (fun S => S ∩ W) he
    apply label_unmarked G R W
    rwa [hm]

/-- Singleton fiber plus fixed neighboring labels preserves the complete
degree, including the reverse assertion that no new neighbor appears. -/
theorem degree_eq_of_fixed_neighbors (v : V)
    (hvM : ¬ (marked G R W v).Nonempty)
    (hfix : ∀ u, G.Adj v u → label G R W u = u) :
    (graph G R W).degree (vertex G R W v) = G.degree v := by
  classical
  have hvfix := label_unmarked G R W hvM
  let D := G.neighborFinset v
  have hinj : Set.InjOn (vertex G R W) (D : Set V) := by
    intro u hu z hz he
    have he' := congrArg Subtype.val he
    change label G R W u = label G R W z at he'
    rw [hfix u ((G.mem_neighborFinset v u).mp hu),
      hfix z ((G.mem_neighborFinset v z).mp hz)] at he'
    exact he'
  have he : (graph G R W).neighborFinset (vertex G R W v) = D.image (vertex G R W) := by
    apply Finset.Subset.antisymm
    · intro r hr
      have har := ((graph G R W).mem_neighborFinset _ _).mp hr
      obtain ⟨_, p, q, hp, hq, hpq⟩ := har
      change label G R W p = label G R W v at hp
      have hpeq : p = v := by
        have hm : p ∈ {u | label G R W u = v} := hp.trans hvfix
        rw [fiber_unmarked G R W v hvfix hvM] at hm
        exact hm
      subst p
      exact Finset.mem_image.mpr ⟨q, (G.mem_neighborFinset v q).mpr hpq, Subtype.ext hq⟩
    · intro r hr
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
      have ha := (G.mem_neighborFinset v u).mp hu
      apply ((graph G R W).mem_neighborFinset _ _).mpr
      apply edge_of_different_labels G R W ha
      rw [hvfix, hfix u ha]
      exact ha.ne
  calc
    (graph G R W).degree (vertex G R W v) =
        ((graph G R W).neighborFinset (vertex G R W v)).card := rfl
    _ = (D.image (vertex G R W)).card := congrArg Finset.card he
    _ = D.card := Finset.card_image_of_injOn hinj
    _ = G.degree v := rfl

/-- Every vertex of an uncontracted component of G-R keeps its degree. -/
theorem degree_uncontracted {v : V} (hvR : v ∉ R)
    (hvM : ¬ (marked G R W v).Nonempty) :
    (graph G R W).degree (vertex G R W v) = G.degree v :=
  degree_eq_of_fixed_neighbors G R W v hvM
    (fun _ ha => neighbor_fixed_of_uncontracted G R W hvR hvM ha)

theorem covered_marks_component (hWR : Disjoint W R) {v : V}
    (hvR : v ∉ R) (hv : v ∈ covered G W) : (marked G R W v).Nonempty := by
  obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
  have hwR : w ∉ R := fun hr => Finset.disjoint_left.mp hWR hw hr
  have hwC : w ∈ cluster G R v := by
    rcases (mem_closed G v w).mp hvw with he | ha
    · rw [he]
      exact cluster_self G R hwR
    · have hc : cluster G R w = cluster G R v :=
        ComponentMap.eq_of_adj G (Finset.univ \ R) w v
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwR⟩)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvR⟩) ha
      rw [← hc]
      exact cluster_self G R hwR
  exact ⟨w, Finset.mem_inter.mpr ⟨hwC, hw⟩⟩

/-- The paper's observation that all original defects outside R are
covered by W forces every uncontracted component to remain d-regular. -/
theorem uncontracted_regular_degree (d : ℕ) (hWR : Disjoint W R)
    (hdef : ∀ v ∉ R, G.degree v ≠ d → v ∈ covered G W)
    {v : V} (hvR : v ∉ R) (hvM : ¬ (marked G R W v).Nonempty) :
    (graph G R W).degree (vertex G R W v) = d := by
  rw [degree_uncontracted G R W hvR hvM]
  by_contra hn
  exact hvM (covered_marks_component G R W hWR hvR (hdef v hvR hn))

/-- In particular, a regular Q vertex whose neighbors all lie in R keeps
its original degree exactly, not merely a lower bound. -/
theorem degree_residual {q : V} (hq : q ∈ R)
    (hneighbors : ∀ v, G.Adj q v → v ∈ R) :
    (graph G R W).degree (vertex G R W q) = G.degree q :=
  degree_eq_of_fixed_neighbors G R W q (unmarked_of_mem G R W hq)
    (fun v hv => label_residual G R W (hneighbors v hv))

noncomputable def contracted : Finset (retained G R W) :=
  Finset.univ.filter (fun r => (marked G R W r.val).Nonempty)

theorem contracted_outside {r : retained G R W} (hr : r ∈ contracted G R W) : r.val ∉ R :=
  marked_nonempty_outside G R W (Finset.mem_filter.mp hr).2

theorem card_image_residual (S : Finset V) (hS : S ⊆ R) :
    (S.image (vertex G R W)).card = S.card := by
  apply Finset.card_image_of_injOn
  intro v hv u hu he
  have he' := congrArg Subtype.val he
  change label G R W v = label G R W u at he'
  rwa [label_residual G R W (hS hv), label_residual G R W (hS hu)] at he'

theorem contracted_disjoint_residual (S : Finset V) (hS : S ⊆ R) :
    Disjoint (contracted G R W) (S.image (vertex G R W)) := by
  apply Finset.disjoint_left.mpr
  intro r hr hSimage
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hSimage
  have hval := congrArg Subtype.val he
  change label G R W v = r.val at hval
  rw [label_residual G R W (hS hv)] at hval
  exact contracted_outside G R W hr (hval ▸ hS hv)

/-- Each contracted component has a different root in W. -/
theorem contracted_card_le : (contracted G R W).card ≤ W.card := by
  classical
  have hsub : contracted G R W ⊆ W.image (vertex G R W) := by
    intro r hr
    have hm := (Finset.mem_filter.mp hr).2
    have hfix := retained_fixed G R W r.property
    have hrW : r.val ∈ W := by
      have hh := (Finset.mem_inter.mp (label_marked G R W hm)).2
      rwa [hfix] at hh
    exact Finset.mem_image.mpr ⟨r.val, hrW, Subtype.ext hfix⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end Paper.ComponentMinor
