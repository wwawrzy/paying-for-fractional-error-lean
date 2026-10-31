import Paper.Endpoints.Girth.CurrentGirthStructure

/-! # Localized face estimates with original crossing-edge counts -/

namespace Paper.MarkedRestriction

open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem interedges_union_left (X Y Z : Finset V) :
    G.interedges (X ∪ Y) Z = G.interedges X Z ∪ G.interedges Y Z := by
  ext p
  simp only [mem_interedges_iff, Finset.mem_union]
  tauto

theorem interedges_union_right (X Y Z : Finset V) :
    G.interedges X (Y ∪ Z) = G.interedges X Y ∪ G.interedges X Z := by
  ext p
  simp only [mem_interedges_iff, Finset.mem_union]
  tauto

theorem inducedEdgeCount_union (X Y : Finset V) (hXY : Disjoint X Y) :
    G.inducedEdgeCount (X ∪ Y) =
      G.inducedEdgeCount X + G.inducedEdgeCount Y + (G.interedges X Y).card := by
  have h : (G.interedges (X ∪ Y) (X ∪ Y)).card =
      ((G.interedges X X).card + (G.interedges X Y).card) +
        ((G.interedges Y X).card + (G.interedges Y Y).card) := by
    rw [interedges_union_left,
      Finset.card_union_of_disjoint (G.interedges_disjoint_left hXY (X ∪ Y)),
      interedges_union_right, interedges_union_right,
      Finset.card_union_of_disjoint (G.interedges_disjoint_right X hXY),
      Finset.card_union_of_disjoint (G.interedges_disjoint_right Y hXY)]
  rw [Incidence.card_interedges_self, Incidence.card_interedges_self,
    Incidence.card_interedges_self, Incidence.card_interedges_comm G Y X] at h
  omega

theorem independent_inducedEdgeCount (A : Finset V)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) : G.inducedEdgeCount A = 0 := by
  have he : G.interedges A A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨ha, hb, hab⟩ := (mem_interedges_iff G).mp hp
    exact hA p.1 ha p.2 hb hab
  have hh := Incidence.card_interedges_self G A
  rw [he, Finset.card_empty] at hh
  omega

/-- Restrict the marked face estimate to A∪T, identifying its marked edges
with the original crossing edges between the two disjoint parts. -/
theorem localized_face_bound
    (hplanar : G.IsPlanar) (A T : Finset V) (hAT : Disjoint A T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b)
    (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v), c.IsCycle → g ≤ c.length) :
    (G.inducedEdgeCount (A ∪ T) : ℝ) ≤
      (g : ℝ) / ((g : ℝ) - 2) * (A.card + T.card) +
        ((g : ℝ) - 3) / ((g : ℝ) - 2) * (G.interedges A T).card := by
  let S := A ∪ T
  let H := G.induce (S : Set V)
  let M : Finset (S : Set V) := Finset.univ.filter fun v => v.val ∈ A
  have hmem (v : (S : Set V)) : v ∈ M ↔ v.val ∈ A := by simp [M]
  have hM : ∀ a ∈ M, ∀ b ∈ M, ¬ H.Adj a b := by
    intro a ha b hb hab
    exact hA a.val ((hmem a).mp ha) b.val ((hmem b).mp hb) hab
  have hdeg (a : (S : Set V)) (ha : a ∈ M) :
      H.degree a = (T.filter (G.Adj a.val)).card := by
    have he : H.neighborFinset a =
        Finset.univ.filter (fun b : (S : Set V) => b.val ∈ T ∧ G.Adj a.val b.val) := by
      ext b
      simp only [mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hab
        have hb := b.property
        rcases Finset.mem_union.mp hb with hbA | hbT
        · exact False.elim (hA a.val ((hmem a).mp ha) b.val hbA hab)
        · exact ⟨hbT, hab⟩
      · exact fun h => h.2
    rw [← card_neighborFinset_eq_degree, he]
    apply Finset.card_bij (fun b _ => b.val)
    · intro b hb
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
    · intro b hb c hc h
      exact Subtype.ext h
    · intro b hb
      refine ⟨⟨b, Finset.mem_union_right A (Finset.mem_filter.mp hb).1⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hp : (CurrentFaceBound.incidentMarkedEdges (G := H) M).card =
      (G.interedges A T).card := by
    rw [CurrentGirthStructure.incident_card_eq_degree_sum H M hM,
      Incidence.card_interedges_eq_sum]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a ha
      exact (hmem a).mp ha
    · intro a ha b hb h
      exact Subtype.ext h
    · intro a ha
      refine ⟨⟨a, Finset.mem_union_left T ha⟩, ?_, rfl⟩
      exact (hmem _).mpr ha
    · exact fun a ha => hdeg a ha
  have hgirthH : ∀ (v : {x : (S : Set V) // x ∉ M})
      (c : (H.induce {x | x ∉ M}).Walk v v), c.IsCycle → g ≤ c.length := by
    intro v c hc
    let f : (H.induce {x | x ∉ M}) →g G.induce {x : V | x ∉ A} :=
      { toFun := fun x => ⟨x.val.val, fun hx => x.property ((hmem x.val).mpr hx)⟩
        map_rel' := fun h => h }
    have hinj : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {x : V // x ∉ A} => z.val) h
    have hc' := (Walk.map_isCycle_iff_of_injective (f := f) hinj).mpr hc
    simpa only [Walk.length_map] using hgirth _ (c.map f) hc'
  have hh := CurrentPlanarFaceBound.real_edge_bound
    (hplanar.induce (S : Set V)) M g hg hgirthH
  rw [hp] at hh
  have hcard : Fintype.card (S : Set V) = A.card + T.card := by
    simpa only [S, Fintype.card_eq_nat_card, Finset.coe_sort_coe,
      Nat.card_eq_finsetCard] using Finset.card_union_of_disjoint hAT
  have he : H.edgeFinset.card = G.inducedEdgeCount S := by
    simp only [H, SimpleGraph.inducedEdgeCount, edgeFinset_card,
      Fintype.card_eq_nat_card]
  rw [he, hcard] at hh
  simpa only [S, Nat.cast_add] using hh

/-- Every induced subgraph avoiding A inherits the girth outside A. -/
theorem induced_density_outside
    (hplanar : G.IsPlanar) (A T : Finset V) (hAT : Disjoint A T)
    (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v), c.IsCycle → g ≤ c.length) :
    (G.inducedEdgeCount T : ℝ) ≤
      (g : ℝ) / ((g : ℝ) - 2) * T.card := by
  have ht : ∀ (v : (T : Set V)) (c : (G.induce (T : Set V)).Walk v v),
      c.IsCycle → g ≤ c.length := by
    intro v c hc
    let f : G.induce (T : Set V) →g G.induce {x : V | x ∉ A} :=
      { toFun := fun x => ⟨x.val, fun hx => Finset.disjoint_left.mp hAT hx x.property⟩
        map_rel' := fun h => h }
    have hinj : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {x : V // x ∉ A} => z.val) h)
    have hc' := (Walk.map_isCycle_iff_of_injective (f := f) hinj).mpr hc
    simpa only [Walk.length_map] using hgirth _ (c.map f) hc'
  have hh := CurrentPlanarFaceBound.girth_edge_bound (hplanar.induce (T : Set V)) g hg ht
  simpa only [SimpleGraph.inducedEdgeCount, edgeFinset_card, Fintype.card_eq_nat_card,
    Finset.coe_sort_coe, Nat.card_eq_finsetCard] using hh

/-- Counting all A--(Q∪L) edges at once permits using the full induced graph,
including A--L and L--L edges. No desired crossing-edge bound is a premise. -/
theorem crossing_bound
    (hplanar : G.IsPlanar) (A Q L : Finset V)
    (hAT : Disjoint A (Q ∪ L)) (hQL : Disjoint Q L)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b)
    (g d : ℕ) (hg : 3 ≤ g)
    (hd : (d : ℝ) = 2 * ((g : ℝ) / ((g : ℝ) - 2)))
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v), c.IsCycle → g ≤ c.length)
    (hQ : ∀ q ∈ Q, d ≤ G.inducedDegree q (Q ∪ L)) :
    ((G.interedges A (Q ∪ L)).card : ℝ) ≤ (g : ℝ) * (A.card + L.card) := by
  have hsumN : d * Q.card ≤ (G.interedges Q (Q ∪ L)).card := by
    rw [Incidence.card_interedges_eq_sum]
    calc
      d * Q.card = ∑ _q ∈ Q, d := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hQ
  have hsum : (d : ℝ) * Q.card ≤ (G.interedges Q (Q ∪ L)).card := by
    exact_mod_cast hsumN
  rw [hd] at hsum
  have hi := Incidence.card_interedges_le G Q (Q ∪ L)
  rw [Finset.union_eq_right.mpr Finset.subset_union_left,
    Finset.inter_eq_left.mpr Finset.subset_union_left] at hi
  have hiR : ((G.interedges Q (Q ∪ L)).card : ℝ) ≤
      G.inducedEdgeCount (Q ∪ L) + G.inducedEdgeCount Q := by exact_mod_cast hi
  have heQ := induced_density_outside G hplanar A Q
    (hAT.mono_right Finset.subset_union_left) g hg hgirth
  have heT : (g : ℝ) / ((g : ℝ) - 2) * Q.card ≤
      G.inducedEdgeCount (Q ∪ L) := by nlinarith only [hsum, hiR, heQ]
  have hf := localized_face_bound G hplanar A (Q ∪ L) hAT hA g hg hgirth
  rw [inducedEdgeCount_union G A (Q ∪ L) hAT,
    independent_inducedEdgeCount G A hA, zero_add,
    Finset.card_union_of_disjoint hQL] at hf
  push_cast at hf
  have hpos : (0 : ℝ) < (g : ℝ) - 2 := by
    have hgr : (3 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  have hs : ((g : ℝ) - 2) *
        (G.inducedEdgeCount (Q ∪ L) + (G.interedges A (Q ∪ L)).card) ≤
      (g : ℝ) * (A.card + (Q.card + L.card)) +
        ((g : ℝ) - 3) * (G.interedges A (Q ∪ L)).card := by
    convert mul_le_mul_of_nonneg_left hf hpos.le using 1 <;>
      field_simp [ne_of_gt hpos]
  have ht : (g : ℝ) * Q.card ≤ ((g : ℝ) - 2) * G.inducedEdgeCount (Q ∪ L) := by
    convert mul_le_mul_of_nonneg_left heT hpos.le using 1 <;>
      field_simp [ne_of_gt hpos]
  nlinarith only [hs, ht]

end Paper.MarkedRestriction

#print axioms Paper.MarkedRestriction.inducedEdgeCount_union
#print axioms Paper.MarkedRestriction.independent_inducedEdgeCount
#print axioms Paper.MarkedRestriction.localized_face_bound
#print axioms Paper.MarkedRestriction.induced_density_outside
#print axioms Paper.MarkedRestriction.crossing_bound
