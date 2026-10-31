import Paper.Optimality.Treewidth.CliqueDensityReduction
import Paper.Optimality.Treewidth.CliqueDegree

/-! The next genuine structural case for K6-free density. Every positive
degree in a four-common-neighbor core is at least six. Thus the bounded
neighborhood reduction leaves orders six, seven and eight. No contradiction
for these remaining cases, or sharp K6-free density, is postulated. -/
namespace Paper.SixCliqueReduction

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_lower_general (t : ℕ) (ht : 3 ≤ t) (hG : G.IsKMinorFree t)
    (v : V) (hv : 0 < G.degree v)
    (hcn : ∀ w, G.Adj v w → t - 2 ≤ Fintype.card (G.commonNeighbors v w)) :
    t ≤ G.degree v := by
  classical
  have hN : 0 < Fintype.card (G.neighborSet v) := by
    rw [G.card_neighborSet_eq_degree]
    exact hv
  letI : Nonempty (G.neighborSet v) := Fintype.card_pos_iff.mp hN
  let J := G.induce (G.neighborSet v)
  have hdeg : ∀ w : G.neighborSet v, t - 2 ≤ J.degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v (t - 2) w (hcn w w.property)
  have hmin : t - 2 ≤ J.minDegree := J.le_minDegree_of_forall_le_degree (t - 2) hdeg
  have hcard : t - 1 ≤ Fintype.card (G.neighborSet v) := by
    have hh := J.minDegree_lt_card
    omega
  by_contra hbound
  have hcardExact : Fintype.card (G.neighborSet v) = t - 1 := by
    rw [G.card_neighborSet_eq_degree] at hcard ⊢
    omega
  have hpred : (t - 1) - 1 = t - 2 := by omega
  have hm := CliqueDegree.complete_minor J (t - 1) hcardExact (by simpa only [hpred] using hdeg)
  have hfree : J.IsKMinorFree (t - 1) :=
    CliqueDensityReduction.neighborhood_exclusion G t ht hG v
  exact hfree hm

theorem degree_lower (hG : G.IsKMinorFree 6) (v : V) (hv : 0 < G.degree v)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) :
    6 ≤ G.degree v := degree_lower_general G 6 (by decide) hG v hv hcn

theorem bounded_neighborhood (hG : G.IsKMinorFree 6) (hV : 0 < Fintype.card V)
    (hdense : 4 * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H.IsMinor G ∧ H.IsKMinorFree 6 ∧
      4 * Fintype.card W = H.edgeFinset.card ∧
      (∀ u w, H.Adj u w → 4 ≤ Fintype.card (H.commonNeighbors u w)) ∧
      ∃ v : W, 6 ≤ H.degree v ∧ H.degree v ≤ 8 ∧
        (H.induce (H.neighborSet v)).IsKMinorFree 5 ∧
        4 ≤ (H.induce (H.neighborSet v)).minDegree := by
  classical
  obtain ⟨W, _, _, H, _, hm, hH, he, hcn, v, hvlo, hvhi, hN, hmin⟩ :=
    CliqueDensityReduction.six G hG hV hdense
  exact ⟨W, inferInstance, inferInstance, H, inferInstance, hm, hH, he, hcn,
    v, degree_lower H hH v (by omega) (hcn v), hvhi, hN, hmin⟩

end Paper.SixCliqueReduction

#print axioms Paper.SixCliqueReduction.degree_lower
#print axioms Paper.SixCliqueReduction.degree_lower_general
#print axioms Paper.SixCliqueReduction.bounded_neighborhood
