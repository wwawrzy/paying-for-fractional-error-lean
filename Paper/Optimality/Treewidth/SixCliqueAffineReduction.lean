import Paper.Optimality.Treewidth.CliqueAffineCore
import Paper.Optimality.Treewidth.SixCliqueReduction

/-! The affine K6 counterexample reduction. Keeping the additive constant
reduces the least-degree cases to six and seven. The necessary global
structural contradiction is not assumed. -/
namespace Paper.SixCliqueAffineReduction

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem extract (hG : G.IsKMinorFree 6) (hV : 4 ≤ Fintype.card V)
    (hdense : 4 * Fintype.card V - 9 ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H.IsMinor G ∧ H.IsKMinorFree 6 ∧
      H.edgeFinset.card + 9 = 4 * Fintype.card W ∧
      (∀ u w, H.Adj u w → 4 ≤ Fintype.card (H.commonNeighbors u w)) ∧
      (∀ u, 6 ≤ H.degree u) ∧
      ∃ v, H.degree v = H.minDegree ∧ (H.degree v = 6 ∨ H.degree v = 7) := by
  classical
  obtain ⟨W, _, _, H, _, hW, he, hp, hc, hm⟩ :=
    CliqueAffineCore.extract G 4 9 4 (by decide) (by decide) (by decide) hV hdense
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hH : H.IsKMinorFree 6 := IsHMinorFree.minor hG hm
  have he' : H.edgeFinset.card + 9 = 4 * Fintype.card W := by omega
  have hdeg : ∀ u, 6 ≤ H.degree u := fun u =>
    SixCliqueReduction.degree_lower H hH u (hp u) (hc u)
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  have hupper : H.minDegree ≤ 7 := by
    have hh := H.minDegree_mul_card_le_two_mul_card_edges
    by_contra hn
    have hlo : 8 ≤ H.minDegree := by omega
    have hmul := Nat.mul_le_mul_right (Fintype.card W) hlo
    omega
  have hvlo := hdeg v
  refine ⟨W, inferInstance, inferInstance, H, inferInstance,
    hm, hH, he', hc, hdeg, v, hv.symm, ?_⟩
  omega

end Paper.SixCliqueAffineReduction

#print axioms Paper.SixCliqueAffineReduction.extract
