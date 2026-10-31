import Paper.Optimality.Treewidth.CliqueExteriorComplementConnected
import Paper.Optimality.Treewidth.CliqueAffineBoundaryBudget
namespace Paper.CliqueExteriorSmallDeletion
open SimpleGraph CliqueComponentBoundary PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem connected (v : V)
    (hboundary : ∀ D : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent,
      4 ≤ (boundary G (outside G (insert v (G.neighborSet v)) D)).card)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (S : Finset V) (hS : S ⊆ G.neighborFinset v) (hsmall : S.card ≤ 3) :
    (G.induce (outside G (insert v (G.neighborSet v)) C ∪ (S : Set V))ᶜ).Connected := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let B := A \ (S : Set V)
  have hSA : (S : Set V) ⊆ A := fun z hz => Or.inr ((G.mem_neighborFinset v z).mp (hS hz))
  have hvS : v ∉ S := fun hh => G.notMem_neighborFinset_self v (hS hh)
  have hvB : v ∈ B := ⟨Or.inl rfl,hvS⟩
  have hB : (G.induce B).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨v,hvB⟩,?_⟩
    intro w
    rcases w.property.1 with heq | hvw
    · have hw : w = ⟨v,hvB⟩ := Subtype.ext heq
      rw [hw]
    · exact (show (G.induce B).Adj ⟨v,hvB⟩ w from hvw).reachable
  have hBR : B ⊆ (X ∪ (S : Set V))ᶜ := by
    intro z hz hh
    rcases hh with hx | hs
    · exact outside_subset G A C hx hz.1
    · exact hz.2 hs
  apply G.induce_connected_of_patches v (hBR hvB)
  intro y hy
  have hyX : y ∉ X := fun hh => hy (Or.inl hh)
  have hyS : y ∉ S := fun hh => hy (Or.inr hh)
  by_cases hyA : y ∈ A
  · have hyB : y ∈ B := ⟨hyA,hyS⟩
    exact ⟨B,hBR,hvB,hyB,hB.preconnected ⟨v,hvB⟩ ⟨y,hyB⟩⟩
  · let D := (G.induce Aᶜ).connectedComponentMk ⟨y,hyA⟩
    let Y := outside G A D
    have hyY : y ∈ Y := ⟨⟨y,hyA⟩,ConnectedComponent.connectedComponentMk_mem,rfl⟩
    have hDC : D ≠ C := by
      intro heq
      apply hyX
      change y ∈ outside G A C
      rw [← heq]
      exact hyY
    have hYX : Y ⊆ Xᶜ := by
      rintro z ⟨a,ha,rfl⟩ ⟨b,hb,hba⟩
      have hab : b = a := Subtype.ext hba
      subst b
      exact hDC (((ConnectedComponent.mem_supp_iff D a).mp ha).symm.trans ((ConnectedComponent.mem_supp_iff C a).mp hb))
    have hYR : Y ⊆ (X ∪ (S : Set V))ᶜ := by
      intro z hz hh
      rcases hh with hx | hs
      · exact hYX hz hx
      · exact outside_subset G A D hz (hSA hs)
    have hex : ∃ p ∈ boundary G Y, p ∉ S := by
      by_contra hn
      push Not at hn
      have hh := Finset.card_le_card (show boundary G Y ⊆ S from hn)
      have hl := hboundary D
      change 4 ≤ (boundary G Y).card at hl
      omega
    obtain ⟨p,hp,hpS⟩ := hex
    have hpB : p ∈ B := ⟨boundary_subset G A D hp,hpS⟩
    obtain ⟨_,z,hz,hpz⟩ := (mem_boundary G Y p).mp hp
    have hBY : (G.induce (B ∪ Y)).Connected :=
      SimpleGraph.connected_induce_union hB.preconnected (outside_connected G A D).preconnected hpB hz hpz
    have hsub : B ∪ Y ⊆ (X ∪ (S : Set V))ᶜ := Set.union_subset hBR hYR
    have hvBY : v ∈ B ∪ Y := Or.inl hvB
    have hyBY : y ∈ B ∪ Y := Or.inr hyY
    exact ⟨B ∪ Y,hsub,hvBY,hyBY,hBY.preconnected ⟨v,hvBY⟩ ⟨y,hyBY⟩⟩
end Paper.CliqueExteriorSmallDeletion
