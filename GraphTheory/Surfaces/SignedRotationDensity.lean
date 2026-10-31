import GraphTheory.Surfaces.SignedRotationSmallGenus
import GraphTheory.Surfaces.SignedRotationGenusSum

/-! Density at Euler genus at most two, without a connectedness hypothesis. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

theorem component_order_sum [Fintype G.ConnectedComponent] :
    Nat.card V = ∑ c : G.ConnectedComponent, Nat.card c.supp := by
  classical
  let e : (Σ c : G.ConnectedComponent, c.supp) ≃ V :=
    Equiv.sigmaFiberEquiv G.connectedComponentMk
  rw [← Nat.card_congr e, Nat.card_sigma]

theorem edge_bound (hg : r.eulerGenus ≤ 2) : G.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have he : (Nat.card r.Edge : ℤ) = ∑ c : G.ConnectedComponent,
      (Nat.card (r.restrictComponent c).Edge : ℤ) := by
    exact_mod_cast r.edge_card_sum
  have hv : (Fintype.card V : ℤ) = ∑ c : G.ConnectedComponent, (Nat.card c.supp : ℤ) := by
    have h := component_order_sum (G := G)
    rw [Nat.card_eq_fintype_card (α := V)] at h
    exact_mod_cast h
  have hgen := r.eulerGenus_sum
  have hb (c : G.ConnectedComponent) : (Nat.card (r.restrictComponent c).Edge : ℤ) ≤
      3 * Nat.card c.supp + 3 * (r.restrictComponent c).eulerGenus := by
    simpa only [edge_card, Nat.card_eq_fintype_card] using
      (r.restrictComponent c).connected_edge_genus_bound c.connected_toSimpleGraph
  by_cases hex : ∃ c : G.ConnectedComponent, 3 ≤ Nat.card c.supp
  · obtain ⟨c₀, hc₀⟩ := hex
    have hsharp : (Nat.card (r.restrictComponent c₀).Edge : ℤ) + 6 ≤
        3 * Nat.card c₀.supp + 3 * (r.restrictComponent c₀).eulerGenus := by
      have h := (r.restrictComponent c₀).connected_euler_edge_bound c₀.connected_toSimpleGraph
        (by simpa only [Nat.card_eq_fintype_card] using hc₀)
      rw [← (r.restrictComponent c₀).edge_card] at h
      rw [Nat.card_eq_fintype_card (α := c₀.supp)]
      omega
    have hall (c : G.ConnectedComponent) :
        (Nat.card (r.restrictComponent c).Edge : ℤ) + (if c = c₀ then 6 else 0) ≤
          3 * Nat.card c.supp + 3 * (r.restrictComponent c).eulerGenus := by
      by_cases h : c = c₀
      · subst c
        simpa using hsharp
      · simpa [h] using hb c
    have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hall c)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hdelta : (∑ c : G.ConnectedComponent, if c = c₀ then (6 : ℤ) else 0) = 6 := by simp
    rw [hdelta, ← he, ← hv, ← hgen, r.edge_card] at hsum
    have hfinal : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V := by omega
    exact_mod_cast hfinal
  · have hall (c : G.ConnectedComponent) : Nat.card (r.restrictComponent c).Edge ≤
        3 * Nat.card c.supp := by
      have hn : Fintype.card c.supp ≤ 2 := by
        have h : ¬ 3 ≤ Nat.card c.supp := fun h => hex ⟨c, h⟩
        simpa only [Nat.card_eq_fintype_card] using (show Nat.card c.supp ≤ 2 by omega)
      have hsmall : ∀ n : ℕ, n ≤ 2 → n.choose 2 ≤ 3 * n := by
        intro n hn
        interval_cases n <;> decide
      rw [(r.restrictComponent c).edge_card, Nat.card_eq_fintype_card]
      exact (G.induce c.supp).card_edgeFinset_le_card_choose_two.trans (hsmall _ hn)
    have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hall c)
    rw [← r.edge_card_sum, ← Finset.mul_sum, ← component_order_sum, r.edge_card,
      Nat.card_eq_fintype_card] at hsum
    exact hsum

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.component_order_sum
#print axioms SimpleGraph.SignedRotation.edge_bound
