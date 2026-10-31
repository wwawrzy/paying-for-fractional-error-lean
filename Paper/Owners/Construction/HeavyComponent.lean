import Paper.Preliminaries.ComponentContainment

/-! Two vertex sets carrying more than half of a nonnegative total weight
intersect. Heavy deletion components consequently nest under deletion. -/
namespace Paper.HeavyComponent
attribute [local instance] Classical.propDecidable
open DeletionComponents
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def mass (w : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, w v

theorem half_intersect (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (S T : Finset V)
    (hS : (∑ v, w v) / 2 < mass w S) (hT : (∑ v, w v) / 2 < mass w T) :
    (S ∩ T).Nonempty := by
  by_contra hn
  have hdis : Disjoint S T := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hs : mass w S + mass w T = mass w (S ∪ T) := (Finset.sum_union hdis).symm
  have ht : mass w (S ∪ T) ≤ ∑ v, w v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hw v)
  linarith

theorem unique (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (X : Finset V)
    (C D : (deleted G X).ConnectedComponent)
    (hC : (∑ v, w v) / 2 < mass w (physical G X C))
    (hD : (∑ v, w v) / 2 < mass w (physical G X D)) : C = D := by
  by_contra hn
  obtain ⟨v, hv⟩ := half_intersect w hw _ _ hC hD
  exact Finset.disjoint_left.mp (DeletionComponents.disjoint G X C D hn)
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2

theorem nested (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (X Y : Finset V) (hXY : X ⊆ Y)
    (C : (deleted G X).ConnectedComponent) (D : (deleted G Y).ConnectedComponent)
    (hC : (∑ v, w v) / 2 < mass w (physical G X C))
    (hD : (∑ v, w v) / 2 < mass w (physical G Y D)) : physical G Y D ⊆ physical G X C := by
  apply ComponentContainment.subset G X C _ (DeletionComponents.connected G Y D)
  · apply Finset.disjoint_left.mpr
    intro v hv hx
    exact Finset.disjoint_left.mp (DeletionComponents.avoids G Y D) hv (hXY hx)
  · exact half_intersect w hw _ _ hD hC
end Paper.HeavyComponent
