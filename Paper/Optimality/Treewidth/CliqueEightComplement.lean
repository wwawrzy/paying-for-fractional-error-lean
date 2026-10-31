import GraphTheory.SimpleGraph.Domination.Bounds

/-! Low-degree complement facts for the remaining eight-vertex case. -/
namespace Paper.CliqueEightComplement
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem independent_triple (hV : Fintype.card V = 8)
    (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ D : Finset V, H.IsIndepSet (D : Set V) → D.card ≤ 3) :
    ∃ D : Finset V, D.card = 3 ∧ H.IsIndependentDominatingSetFinset D := by
  obtain ⟨D, hD⟩ := H.exists_independentDominatingSetFinset
  have hu := hsmall D hD.2
  have hl := hD.1.card_mul_maxDegree_add_one_le
  have hm := H.maxDegree_le_of_forall_degree_le 2 hd
  have hn : 8 ≤ D.card * 3 := by
    calc
      8 = Fintype.card V := hV.symm
      _ ≤ D.card * (H.maxDegree + 1) := hl
      _ ≤ D.card * 3 := Nat.mul_le_mul_left _ (by omega)
  exact ⟨D, by omega, hD⟩

theorem triangle_neighbors (hd : ∀ x, H.degree x ≤ 2)
    (S : Finset V) (hS : S.card = 3) (hclique : H.IsClique (S : Set V))
    (x : V) (hx : x ∈ S) : H.neighborFinset x = S.erase x := by
  have hsub : S.erase x ⊆ H.neighborFinset x := by
    intro y hy
    obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy
    exact (H.mem_neighborFinset x y).mpr (hclique hx hyS hyx.symm)
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_erase_of_mem hx, hS, H.card_neighborFinset_eq_degree]
  exact hd x

theorem triangle_closed (hd : ∀ x, H.degree x ≤ 2)
    (S : Finset V) (hS : S.card = 3) (hclique : H.IsClique (S : Set V))
    (x : V) (hx : x ∈ S) (y : V) (hxy : H.Adj x y) : y ∈ S := by
  have hy := (H.mem_neighborFinset x y).mpr hxy
  rw [triangle_neighbors H hd S hS hclique x hx] at hy
  exact (Finset.mem_erase.mp hy).2

end Paper.CliqueEightComplement
#print axioms Paper.CliqueEightComplement.independent_triple
#print axioms Paper.CliqueEightComplement.triangle_neighbors
#print axioms Paper.CliqueEightComplement.triangle_closed
