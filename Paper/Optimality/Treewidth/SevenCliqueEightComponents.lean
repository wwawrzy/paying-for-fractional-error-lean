import Paper.Optimality.Treewidth.SevenCliqueEightNeighbors
import Paper.Optimality.Treewidth.CliqueNeighborhoodExterior
namespace Paper.SevenCliqueEightComponents
open SimpleGraph CliqueComponentBoundary PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem pair (hG : G.IsKMinorFree 7)
    (v : V) (hv : G.degree v = 8) (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V) :
    ∃ C D : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent, C ≠ D := by
  classical
  have hn := SevenCliqueEightNeighbors.exterior_not_connected G hG v hv hmin hcn
  obtain ⟨X,hX,hne,hout,hb⟩ := CliqueNeighborhoodExterior.exists_exterior G v hproper
  obtain ⟨z,hz⟩ := hne
  let x : ↥((insert v (G.neighborSet v) : Set V)ᶜ) := ⟨z,hout hz⟩
  let H := G.induce (insert v (G.neighborSet v))ᶜ
  have hnot : ¬∀ y, H.Reachable x y := by
    intro hh
    exact hn (H.connected_iff_exists_forall_reachable.mpr ⟨x,hh⟩)
  obtain ⟨y,hxy⟩ := not_forall.mp hnot
  refine ⟨H.connectedComponentMk x,H.connectedComponentMk y,?_⟩
  exact fun he => hxy (ConnectedComponent.eq.mp he)
theorem separated_pair (hG : G.IsKMinorFree 7)
    (v : V) (hv : G.degree v = 8) (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S)) :
    ∃ C D : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent,
      C ≠ D ∧
      Disjoint (outside G (insert v (G.neighborSet v)) C) (outside G (insert v (G.neighborSet v)) D) ∧
      (∀ x ∈ outside G (insert v (G.neighborSet v)) C,
        ∀ y ∈ outside G (insert v (G.neighborSet v)) D, ¬G.Adj x y) ∧
      ¬G.IsClique (boundary G (outside G (insert v (G.neighborSet v)) C) : Set V) ∧
      ¬G.IsClique (boundary G (outside G (insert v (G.neighborSet v)) D) : Set V) := by
  classical
  obtain ⟨C,D,hCD⟩ := pair G hG v hv hmin hcn hproper
  let A : Set V := insert v (G.neighborSet v)
  have hnon (E : (G.induce Aᶜ).ConnectedComponent) : (outside G A E).Nonempty := by
    obtain ⟨z,hz⟩ := E.nonempty_supp
    exact ⟨z.val,z,hz,rfl⟩
  have hcl (E : (G.induce Aᶜ).ConnectedComponent) : ¬G.IsClique (boundary G (outside G A E) : Set V) :=
    CliqueNeighborhoodExterior.boundary_not_clique G v (outside G A E) (hnon E) (outside_subset G A E) hsep
  refine ⟨C,D,hCD,?_,?_,hcl C,hcl D⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,rfl⟩ ⟨b,hb,hba⟩
    have he : b = a := Subtype.ext hba
    subst b
    exact hCD (((ConnectedComponent.mem_supp_iff C a).mp ha).symm.trans ((ConnectedComponent.mem_supp_iff D a).mp hb))
  · rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hadj
    have hh : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hadj
    exact hCD (((ConnectedComponent.mem_supp_iff C b).mp hh).symm.trans ((ConnectedComponent.mem_supp_iff D b).mp hb))
end Paper.SevenCliqueEightComponents
#print axioms Paper.SevenCliqueEightComponents.pair
#print axioms Paper.SevenCliqueEightComponents.separated_pair
