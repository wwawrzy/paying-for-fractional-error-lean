import Paper.Optimality.Treewidth.CliqueDenseCore

/-! A genuine reduction of a hypothetical dense excluded-clique graph.
The core is an actual minor; its chosen neighborhood has bounded order,
minimum degree at least k, and excludes the next smaller complete minor.
This is a reduction theorem, not a sharp density theorem for K6 or above. -/
namespace Paper.CliqueDensityReduction

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem neighborhood_exclusion (h : ℕ) (hh : 3 ≤ h)
    (hG : G.IsKMinorFree h) (v : V) :
    (G.induce (G.neighborSet v)).IsKMinorFree (h - 1) := by
  intro hm
  exact existingNeighborhoodExtensionProof% G v h hh (fun hf => hf hm) hG

def Profile (h k : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (H : SimpleGraph W) (_ : DecidableRel H.Adj),
    H.IsMinor G ∧ H.IsKMinorFree (h + 1) ∧
    k * Fintype.card W = H.edgeFinset.card ∧
    (∀ v w, H.Adj v w → k ≤ Fintype.card (H.commonNeighbors v w)) ∧
    ∃ v : W, k + 1 ≤ H.degree v ∧ H.degree v ≤ 2 * k ∧
      (H.induce (H.neighborSet v)).IsKMinorFree h ∧
      k ≤ (H.induce (H.neighborSet v)).minDegree

theorem extract (h : ℕ) (hh : 2 ≤ h) (k : ℕ) (hk : 0 < k)
    (hG : G.IsKMinorFree (h + 1)) (hV : 0 < Fintype.card V)
    (hdense : k * Fintype.card V ≤ G.edgeFinset.card) : Profile G h k := by
  classical
  obtain ⟨W, _, _, H, _, hW, hexact, hpositive, hcn, hm⟩ :=
    CliqueDenseCore.extract G k hk hV hdense
  letI : Nonempty W := Fintype.card_pos_iff.mp hW
  have hH : H.IsKMinorFree (h + 1) := IsHMinorFree.minor hG hm
  obtain ⟨v, hvmin⟩ := H.exists_minimal_degree_vertex
  have hmin : H.minDegree ≤ 2 * k := by
    have hb := H.minDegree_mul_card_le_two_mul_card_edges
    rw [← hexact] at hb
    nlinarith
  have hvupper : H.degree v ≤ 2 * k := by rwa [← hvmin]
  have hN : 0 < Fintype.card (H.neighborSet v) := by
    rw [H.card_neighborSet_eq_degree]
    exact hpositive v
  letI : Nonempty (H.neighborSet v) := Fintype.card_pos_iff.mp hN
  let J := H.induce (H.neighborSet v)
  have hdegrees : ∀ w : H.neighborSet v, k ≤ J.degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree H v k w (hcn v w w.property)
  have hJmin : k ≤ J.minDegree := J.le_minDegree_of_forall_le_degree k hdegrees
  have hvlow : k + 1 ≤ H.degree v := by
    have hj := J.minDegree_lt_card
    rw [H.card_neighborSet_eq_degree] at hj
    omega
  have hfreeN : J.IsKMinorFree h := by
    simpa only [Nat.add_sub_cancel] using neighborhood_exclusion H (h + 1) (by omega) hH v
  exact ⟨W, inferInstance, inferInstance, H, inferInstance,
    hm, hH, hexact, hcn, v, hvlow, hvupper, hfreeN, hJmin⟩

/-- A K6-free counterexample to density four has an actual contraction core
with a K5-free neighborhood on five to eight vertices and minimum degree four.
The remaining structural analysis of that core is not assumed here. -/
theorem six (hG : G.IsKMinorFree 6) (hV : 0 < Fintype.card V)
    (hdense : 4 * Fintype.card V ≤ G.edgeFinset.card) : Profile G 5 4 :=
  extract G 5 (by decide) 4 (by decide) hG hV hdense

end Paper.CliqueDensityReduction

#print axioms Paper.CliqueDensityReduction.neighborhood_exclusion
#print axioms Paper.CliqueDensityReduction.extract
#print axioms Paper.CliqueDensityReduction.six
