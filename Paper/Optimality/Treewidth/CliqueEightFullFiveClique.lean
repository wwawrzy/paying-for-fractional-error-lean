import Paper.Optimality.Treewidth.CliqueThreeConnectedOrIsolated
import Paper.Optimality.Treewidth.CliqueConnectedApex
namespace Paper.CliqueEightFullFiveClique
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (hd : ∀ x, 5 ≤ G.degree x) (S : Finset V) (hS : S.card = 5)
    (hcl : G.IsClique (S : Set V)) : False := by
  classical
  have hSc : Fintype.card (S : Set V) = 5 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hS
  let e : Fin 5 ≃ (S : Set V) := Fintype.equivOfCardEq (by simpa using hSc.symm)
  let f : Fin 5 → V := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let m : MinorModel (completeGraph (Fin 5)) G := {
    branchSet := fun i => {f i}
    nonempty := fun i => ⟨f i,rfl⟩
    disjoint := by intro i j hij; rw [Set.disjoint_singleton]; exact hf.ne hij
    connected := by
      intro i
      rw [connected_iff_exists_forall_reachable]
      exact ⟨⟨f i,rfl⟩,fun ⟨z,hz⟩ => by
        rw [Set.mem_singleton_iff] at hz; subst z; exact Reachable.refl _⟩
    adjacent := by
      intro i j hij
      exact ⟨f i,rfl,f j,rfl,hcl (e i).property (e j).property (hf.ne hij)⟩ }
  let R : Set V := (S : Set V)ᶜ
  have hR : Fintype.card R = 3 := by simp [R,Fintype.card_compl_set,hV,hS]
  have hsingle (x : V) : (G.induce ({x} : Set V)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨x,rfl⟩,fun ⟨z,hz⟩ => by
      rw [Set.mem_singleton_iff] at hz; subst z; exact Reachable.refl _⟩
  have hX : ∃ X : Set V, X.Nonempty ∧ (G.induce X).Connected ∧ X ⊆ R ∧
      ∀ i : Fin 5, ∃ x ∈ X, G.Adj x (f i) := by
    rcases CliqueThreeConnectedOrIsolated.of_card (G.induce R) hR with hc | ⟨z,hz⟩
    · let z0 : R := Classical.choice hc.nonempty
      have hne : R.Nonempty := ⟨z0.val,z0.property⟩
      refine ⟨R,hne,hc,Set.Subset.rfl,?_⟩
      intro i
      have hi : f i ∈ S := (e i).property
      have hex : ∃ x ∈ G.neighborFinset (f i), x ∉ S := by
        by_contra hn
        push Not at hn
        have hsub : G.neighborFinset (f i) ⊆ S.erase (f i) := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hx).ne.symm,hn x hx⟩
        have hh := Finset.card_le_card hsub
        rw [G.card_neighborFinset_eq_degree,Finset.card_erase_of_mem hi,hS] at hh
        have hl := hd (f i)
        omega
      obtain ⟨x,hx,hxS⟩ := hex
      exact ⟨x,hxS,((G.mem_neighborFinset _ _).mp hx).symm⟩
    · have hsub : G.neighborFinset z.val ⊆ S := by
        intro y hy
        by_contra hyS
        exact hz ⟨y,hyS⟩ ((G.mem_neighborFinset _ _).mp hy)
      have heq : G.neighborFinset z.val = S := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [G.card_neighborFinset_eq_degree,hS]
        exact hd z.val
      refine ⟨{z.val},⟨z.val,rfl⟩,hsingle z.val,?_,?_⟩
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ z.property
      · intro i
        refine ⟨z.val,rfl,?_⟩
        apply (G.mem_neighborFinset _ _).mp
        rw [heq]
        exact (e i).property
  obtain ⟨X,hne,hconn,hsub,htouch⟩ := hX
  have havoid : ∀ i, Disjoint X (m.branchSet i) := by
    intro i
    rw [Set.disjoint_left]
    intro x hx hxi
    change x = f i at hxi
    have hxS : x ∉ S := hsub hx
    exact hxS (hxi ▸ (e i).property)
  have htouch' : ∀ i, ∃ x ∈ X, ∃ z ∈ m.branchSet i, G.Adj x z := by
    intro i
    obtain ⟨x,hx,hxi⟩ := htouch i
    exact ⟨x,hx,f i,rfl,hxi⟩
  have hfree := CliqueConnectedApex.excludes_set 6 (by decide) hG m X hne hconn havoid htouch'
  exact hfree (IsMinor.refl _)
end Paper.CliqueEightFullFiveClique
