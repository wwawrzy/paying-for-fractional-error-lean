import Paper.Optimality.Treewidth.CliqueComponentBoundary

/-! A genuine component outside a proper closed neighborhood. Its external
boundary lies in the original open neighborhood. If clique separators are
excluded, this boundary contains a real missing edge. -/
namespace Paper.CliqueNeighborhoodExterior

open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_exterior (v : V) (horder : G.degree v + 1 < Fintype.card V) :
    ∃ X : Set V, (G.induce X).Connected ∧ X.Nonempty ∧
      X ⊆ (insert v (G.neighborSet v))ᶜ ∧
      (boundary G X : Set V) ⊆ G.neighborSet v := by
  classical
  let A : Set V := insert v (G.neighborSet v)
  have hex : ∃ x, x ∉ A := by
    by_contra hn
    push Not at hn
    have heq : insert v (G.neighborFinset v) = Finset.univ := by
      ext x
      simp only [Finset.mem_insert, G.mem_neighborFinset, Finset.mem_univ, iff_true]
      exact hn x
    have hsize := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
      G.card_neighborFinset_eq_degree, Finset.card_univ] at hsize
    omega
  obtain ⟨x, hx⟩ := hex
  let C := (G.induce Aᶜ).connectedComponentMk ⟨x, hx⟩
  let X := outside G A C
  have hX : (G.induce X).Connected := outside_connected G A C
  have hXA : X ⊆ Aᶜ := outside_subset G A C
  have hno : ∀ z ∈ X, ¬G.Adj v z := by
    intro z hz hadj
    exact hXA hz (Or.inr hadj)
  refine ⟨X, hX, ?_, hXA, ?_⟩
  · obtain ⟨z, hz⟩ := C.nonempty_supp
    exact ⟨z.val, z, hz, rfl⟩
  · intro y hy
    have hyA : y ∈ A := boundary_subset G A C hy
    rcases hyA with hyv | hyN
    · subst y
      obtain ⟨_, z, hz, hvz⟩ := (mem_boundary G X v).mp hy
      exact False.elim (hno z hz hvz)
    · exact hyN

theorem boundary_not_clique (v : V) (X : Set V) (hX : X.Nonempty)
    (hout : X ⊆ (insert v (G.neighborSet v))ᶜ)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S)) :
    ¬G.IsClique (boundary G X : Set V) := by
  classical
  have hv : v ∉ X := fun hh => hout hh (Set.mem_insert _ _)
  have hno : ∀ z ∈ X, ¬G.Adj v z := by
    intro z hz hadj
    exact hout hz (Or.inr hadj)
  intro hclique
  exact (hsep (boundary G X) hclique).false (separation G X hX v hv hno)

end Paper.CliqueNeighborhoodExterior

#print axioms Paper.CliqueNeighborhoodExterior.exists_exterior
#print axioms Paper.CliqueNeighborhoodExterior.boundary_not_clique
