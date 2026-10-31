import Paper.Optimality.Treewidth.CliqueAffineSeparation
import Paper.Optimality.Treewidth.SevenCliqueSevenNeighbors

/-! A genuine global reduction for the sharp K7 problem. The remaining
least degrees are eight and nine. This theorem retains those cases as
open structural obligations and does not assert the desired density. -/
namespace Paper.SevenCliqueGlobalReduction

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem extract (hG : G.IsKMinorFree 7) (hV : 5 ≤ Fintype.card V)
    (hdense : 5 * Fintype.card V - 14 ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H.IsMinor G ∧ H.IsKMinorFree 7 ∧ 10 ≤ Fintype.card W ∧
      H.edgeFinset.card + 14 = 5 * Fintype.card W ∧
      (∀ u w, H.Adj u w → 5 ≤ Fintype.card (H.commonNeighbors u w)) ∧
      (∀ u, 8 ≤ H.degree u) ∧
      CliqueMinorMinimal.BelowThreshold H 5 14 5 ∧
      (∀ S : Finset W, H.IsClique (S : Set W) → IsEmpty (Separation H S)) ∧
      (∀ u, H.degree u + 1 < Fintype.card W) ∧
      ∃ v, H.degree v = H.minDegree ∧ (H.degree v = 8 ∨ H.degree v = 9) := by
  classical
  obtain ⟨W, _, _, H, _, hW, he, hp, hc, hm, hminimal⟩ :=
    CliqueMinorMinimal.extract G 5 14 5 (by decide) (by decide) (by decide) hV hdense
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hH : H.IsKMinorFree 7 := IsHMinorFree.minor hG hm
  have he' : H.edgeFinset.card + 14 = 5 * Fintype.card W := by omega
  have hdeg : ∀ u, 7 ≤ H.degree u := fun u =>
    SixCliqueReduction.degree_lower_general H 7 (by decide) hH u (hp u) (hc u)
  have hsep : ∀ S : Finset W, H.IsClique (S : Set W) → IsEmpty (Separation H S) := by
    intro S hS
    exact CliqueAffineSeparation.no_clique_separator H 5 14 5 he'
      (fun u => by have hh := hdeg u; omega) hminimal
      CliqueAffineSeparation.five_choose_bound S hS
  have hproper : ∀ u, H.degree u + 1 < Fintype.card W := fun u =>
    SevenCliqueProjection.proper_neighborhood H hH (by omega) he' u
  have hdeg8 : ∀ u, 8 ≤ H.degree u := by
    intro u
    have hh := hdeg u
    by_contra hn
    have hu : H.degree u = 7 := by omega
    exact SevenCliqueSevenNeighbors.impossible H hH hsep u hu (hproper u) (hc u)
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  have hupper : H.minDegree ≤ 9 := by
    have hh := H.minDegree_mul_card_le_two_mul_card_edges
    by_contra hn
    have hlo : 10 ≤ H.minDegree := by omega
    have hmul := Nat.mul_le_mul_right (Fintype.card W) hlo
    omega
  have hvlo := hdeg8 v
  have hvproper := hproper v
  refine ⟨W, inferInstance, inferInstance, H, inferInstance,
    hm, hH, by omega, he', hc, hdeg8, hminimal, hsep, hproper, v, hv.symm, by omega⟩

end Paper.SevenCliqueGlobalReduction

#print axioms Paper.SevenCliqueGlobalReduction.extract
