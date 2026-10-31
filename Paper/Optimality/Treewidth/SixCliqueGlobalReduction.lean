import Paper.Optimality.Treewidth.CliqueMinimalSeparation
import Paper.Optimality.Treewidth.SixCliqueNineVertices

/-! The actual global K6 counterexample retained for the remaining two
structural cases. No density conclusion or separator model is assumed. -/
namespace Paper.SixCliqueGlobalReduction

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem extract (hG : G.IsKMinorFree 6) (hV : 4 ≤ Fintype.card V)
    (hdense : 4 * Fintype.card V - 9 ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H.IsMinor G ∧ H.IsKMinorFree 6 ∧ 10 ≤ Fintype.card W ∧
      H.edgeFinset.card + 9 = 4 * Fintype.card W ∧
      (∀ u w, H.Adj u w → 4 ≤ Fintype.card (H.commonNeighbors u w)) ∧
      (∀ u, 6 ≤ H.degree u) ∧
      CliqueMinorMinimal.BelowThreshold H 4 9 4 ∧
      (∀ S : Finset W, H.IsClique (S : Set W) → IsEmpty (Separation H S)) ∧
      ∃ v, H.degree v = H.minDegree ∧ (H.degree v = 6 ∨ H.degree v = 7) := by
  classical
  obtain ⟨W, _, _, H, _, hW, he, hp, hc, hm, hminimal⟩ :=
    CliqueMinorMinimal.extract G 4 9 4 (by decide) (by decide) (by decide) hV hdense
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hH : H.IsKMinorFree 6 := IsHMinorFree.minor hG hm
  have he' : H.edgeFinset.card + 9 = 4 * Fintype.card W := by omega
  have hdeg : ∀ u, 6 ≤ H.degree u := fun u =>
    SixCliqueReduction.degree_lower H hH u (hp u) (hc u)
  have horder : 10 ≤ Fintype.card W := by
    by_contra hn
    have hb := SixCliqueNineVertices.edge_bound H hH (by omega) (by omega)
    omega
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  have hupper : H.minDegree ≤ 7 := by
    have hh := H.minDegree_mul_card_le_two_mul_card_edges
    by_contra hn
    have hlo : 8 ≤ H.minDegree := by omega
    have hmul := Nat.mul_le_mul_right (Fintype.card W) hlo
    omega
  have hvlo := hdeg v
  refine ⟨W, inferInstance, inferInstance, H, inferInstance,
    hm, hH, horder, he', hc, hdeg, hminimal, ?_, v, hv.symm, by omega⟩
  intro S hS
  exact CliqueMinimalSeparation.no_clique_separator H he'
    (fun u => by have hh := hdeg u; omega) hminimal S hS

end Paper.SixCliqueGlobalReduction

#print axioms Paper.SixCliqueGlobalReduction.extract
