import Paper.Optimality.Treewidth.SixCliqueSharp

/-! Actual rooted projections in K7-free graphs obey the proved K6 edge
bound. In particular an affine K7 counterexample has no universal vertex. -/
namespace Paper.SevenCliqueProjection

open SimpleGraph CliqueStarProjection
variable {V U : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def induced_model (A : Set V) : MinorModel (G.induce A) G where
  branchSet a := {a.val}
  nonempty a := Set.singleton_nonempty a.val
  disjoint a b hab := by
    rw [Set.disjoint_singleton]
    exact fun h => hab (Subtype.ext h)
  connected a := (MinorModel.refl G).connected a.val
  adjacent a b hab := ⟨a.val, rfl, b.val, rfl, hab⟩

theorem edge_bound [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj]
    (hG : G.IsKMinorFree 7) (m : MinorModel H G) (v : V)
    (havoid : ∀ a, v ∉ m.branchSet a)
    (htouch : ∀ a, ∃ z ∈ m.branchSet a, G.Adj v z)
    (hU : 4 ≤ Fintype.card U) : H.edgeFinset.card ≤ 4 * Fintype.card U - 10 :=
  SixCliqueSharp.edge_bound H
    (CliqueRootedProjection.excludes 7 (by decide) hG m v havoid htouch) hU

theorem star_bound (hG : G.IsKMinorFree 7) (v : V)
    (A : Set V) [Fintype A] (hA : A ⊆ G.neighborSet v)
    (u : A) (S : Set V) (huS : u.val ∈ S) (hS : (G.induce S).Connected)
    (hside : ∀ z ∈ S, z ∈ A → z = u.val) (hvS : v ∉ S)
    (hsize : 4 ≤ Fintype.card A) :
    (fill G A u S).edgeFinset.card ≤ 4 * Fintype.card A - 10 := by
  classical
  let m := model G A u S huS hS hside
  have hvA : v ∉ A := fun hh => G.loopless.irrefl v (hA hh)
  have hself (a : A) : a.val ∈ m.branchSet a := by
    dsimp only [m, CliqueStarProjection.model]
    split
    · rename_i ha
      subst a
      exact huS
    · rfl
  have havoid (a : A) : v ∉ m.branchSet a := by
    dsimp only [m, CliqueStarProjection.model]
    split
    · exact hvS
    · intro hh
      exact hvA ((show v = a.val from hh).symm ▸ a.property)
  exact edge_bound G _ hG m v havoid
    (fun a => ⟨a.val, hself a, hA a.property⟩) hsize

theorem proper_neighborhood (hG : G.IsKMinorFree 7)
    (horder : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card + 14 = 5 * Fintype.card V) (v : V) :
    G.degree v + 1 < Fintype.card V := by
  classical
  by_contra hn
  have hvlt := G.degree_lt_card_verts v
  have hv : G.degree v = Fintype.card V - 1 := by omega
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun hh => G.loopless.irrefl v
      (hh ▸ (G.mem_neighborFinset v w).mp hw), Finset.mem_univ _⟩
  have heq : G.neighborFinset v = Finset.univ.erase v :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        G.card_neighborFinset_eq_degree, hv])
  have hfull : ∀ w, w ≠ v → G.Adj v w := by
    intro w hw
    apply (G.mem_neighborFinset v w).mp
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩
  let A : Set V := ({v} : Set V)ᶜ
  have hcard : Fintype.card A = Fintype.card V - 1 := by
    dsimp only [A]
    rw [Fintype.card_compl_set, Set.card_singleton]
  have hbound := edge_bound G (G.induce A) hG (induced_model G A) v
    (fun a hh => a.property (show v = a.val from hh).symm)
    (fun a => ⟨a.val, rfl, hfull a.val (fun hh => a.property hh)⟩) (by omega)
  have hedge : (G.induce A).edgeFinset.card = G.edgeFinset.card - G.degree v := by
    dsimp only [A]
    rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
  rw [hedge, hcard, hv] at hbound
  omega

end Paper.SevenCliqueProjection

#print axioms Paper.SevenCliqueProjection.induced_model
#print axioms Paper.SevenCliqueProjection.edge_bound
#print axioms Paper.SevenCliqueProjection.star_bound
#print axioms Paper.SevenCliqueProjection.proper_neighborhood
