import GraphTheory.Surfaces.SignedRotationDensity

/-! Additive density for an arbitrary finite signed rotation system.
The bound sums the existing connected estimates over all graph components,
including isolated vertices. No connectedness or nonemptiness is required.
This is a combinatorial component of `fv:imp:euler`, not a topological bridge. -/

namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

/-- The additive Euler-genus density bound, with integer arithmetic. -/
theorem edge_genus_bound :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V + 3 * r.eulerGenus := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have he : (Nat.card r.Edge : ℤ) = ∑ c : G.ConnectedComponent,
      (Nat.card (r.restrictComponent c).Edge : ℤ) := by
    exact_mod_cast r.edge_card_sum
  have hv : (Fintype.card V : ℤ) =
      ∑ c : G.ConnectedComponent, (Nat.card c.supp : ℤ) := by
    have h := component_order_sum (G := G)
    rw [Nat.card_eq_fintype_card (α := V)] at h
    exact_mod_cast h
  have hgen := r.eulerGenus_sum
  have hb (c : G.ConnectedComponent) :
      (Nat.card (r.restrictComponent c).Edge : ℤ) ≤
        3 * Nat.card c.supp + 3 * (r.restrictComponent c).eulerGenus := by
    simpa only [edge_card, Nat.card_eq_fintype_card] using
      (r.restrictComponent c).connected_edge_genus_bound c.connected_toSimpleGraph
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hb c)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← he, ← hv, ← hgen, r.edge_card] at hsum
  exact hsum

/-- A natural upper bound on the combinatorial Euler genus gives a natural
edge bound, still valid for disconnected and empty graphs. -/
theorem edge_bound_of_genus_le (e : ℕ) (hg : r.eulerGenus ≤ (e : ℤ)) :
    G.edgeFinset.card ≤ 3 * Fintype.card V + 3 * e := by
  have h := r.edge_genus_bound
  have hbound : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V + 3 * (e : ℤ) := by
    omega
  exact_mod_cast hbound

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.edge_genus_bound
#print axioms SimpleGraph.SignedRotation.edge_bound_of_genus_le
