import Paper.Endpoints.Girth.HighGirthDilutionConnected
import Paper.Endpoints.Girth.HighGirthDensityPartitions

/-! fv:hg:dilute, including arbitrary components and actual subgraphs. -/
namespace Paper.HighGirthDilution
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem minor_induce {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (rho : Real) (h : MinorDensity.Bound G rho) (S : Set V) :
    MinorDensity.Bound (G.induce S) rho := by
  intro A _ _ J _ hm
  exact h A J (hm.trans (SimpleGraph.IsMinor.of_induce G S))

set_option backward.isDefEq.respectTransparency false in
theorem girth_induce {V : Type} (G : SimpleGraph V) (g : Nat)
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → g < p.length) (S : Set V) :
    ∀ (v : S) (p : (G.induce S).Walk v v), p.IsCycle → g < p.length := by
  intro v p hp
  have hh := h v.val (p.map (SimpleGraph.Embedding.induce _).toHom)
    (hp.map Subtype.val_injective)
  simpa only [SimpleGraph.Walk.length_map] using hh

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem density {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (rho : Real) (hrho : 1 ≤ rho) (r : Nat) (hr : 1 ≤ r)
    (hminor : MinorDensity.Bound G rho)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 8*r+2 < p.length) :
    (G.edgeFinset.card : Real) ≤ (1 + (rho-1)/(r+1)) * Fintype.card V := by
  classical
  have hmain : ∀ n, ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W),
      MinorDensity.Bound H rho →
      (∀ (v : W) (p : H.Walk v v), p.IsCycle → 8*r+2 < p.length) →
      Fintype.card W = n →
      (H.edgeFinset.card : Real) ≤ (1 + (rho-1)/(r+1)) * Fintype.card W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hm hg hn
      by_cases hne : Nonempty W
      · letI : Nonempty W := hne
        let v := Classical.arbitrary W
        let K := H.connectedComponentMk v
        let S := K.supp
        have hv : v ∈ S := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        have hclosed : ∀ u ∈ S, ∀ w, H.Adj u w → w ∈ S := by
          intro u hu w he
          exact (K.mem_supp_congr_adj he).mp hu
        have hsmall : Fintype.card (Sᶜ : Set W) < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simpa only [Set.mem_compl_iff,not_not] using hv)
        have hS := HighGirthDilutionConnected.density_connected (H.induce S)
          K.connected_toSimpleGraph rho hrho r hr (minor_induce H rho hm S)
          (girth_induce H (8*r+2) hg S)
        have hrest := ih (Fintype.card (Sᶜ : Set W)) hsmall (H.induce Sᶜ)
          (minor_induce H rho hm Sᶜ) (girth_induce H (8*r+2) hg Sᶜ) rfl
        have hedges := HighGirthDensityPartitions.edge_split H S hclosed
        have hvert := HighGirthDensityPartitions.vertex_split S
        simp only [SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card] at hS hrest hedges hvert ⊢
        have he' : (Nat.card H.edgeSet:Real) = Nat.card (H.induce S).edgeSet + Nat.card (H.induce Sᶜ).edgeSet := by exact_mod_cast hedges
        have hv' : (Nat.card S:Real) + Nat.card (Sᶜ : Set W) = Nat.card W := by exact_mod_cast hvert
        have hscale := congrArg (fun z : Real => (1 + (rho-1)/(r+1))*z) hv'
        dsimp only at hscale
        rw [mul_add] at hscale
        linarith only [hS,hrest,he',hscale]
      · letI : IsEmpty W := not_nonempty_iff.mp hne
        have hz : H = ⊥ := by ext u v; exact isEmptyElim u
        simp [hz]
  exact hmain (Fintype.card V) G hminor hgirth rfl

theorem minor_of_injective {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hinj : Function.Injective f) : SimpleGraph.IsMinor H G := by
  refine ⟨{
    branchSet := fun w => {f w}
    nonempty := fun w => ⟨f w,rfl⟩
    disjoint := ?_
    connected := ?_
    adjacent := ?_ }⟩
  · intro u v hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hne (hinj (hx.symm.trans hy))
  · intro w
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨f w,rfl⟩,?_⟩
    rintro ⟨v,hv⟩
    have heq : v = f w := hv
    subst v
    exact SimpleGraph.Reachable.refl _
  · intro u v he
    exact ⟨f u,rfl,f v,rfl,f.map_adj he⟩

set_option backward.isDefEq.respectTransparency false in
theorem subgraph_density {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (rho : Real) (hrho : 1 ≤ rho)
    (r : Nat) (hr : 1 ≤ r) (hminor : MinorDensity.Bound G rho)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 8*r+2 < p.length)
    (H : SimpleGraph W) (f : H →g G) (hinj : Function.Injective f) :
    (H.edgeFinset.card : Real) ≤ (1 + (rho-1)/(r+1)) * Fintype.card W := by
  classical
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hm : MinorDensity.Bound H rho := by
    intro A _ _ J _ hJ
    exact hminor A J (hJ.trans (minor_of_injective f hinj))
  have hg : ∀ (v : W) (p : H.Walk v v), p.IsCycle → 8*r+2 < p.length := by
    intro v p hp
    have hh := hgirth (f v) (p.map f) (hp.map hinj)
    simpa only [SimpleGraph.Walk.length_map] using hh
  have hh := density H rho hrho r hr hm hg
  simpa only [SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card] using hh

/- The full fv:hg:dilute assertion, for every actual subgraph. -/
set_option backward.isDefEq.respectTransparency false in
theorem all_subgraphs {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (rho : Real) (hrho : 1 ≤ rho) (r : Nat) (hr : 1 ≤ r)
    (hminor : MinorDensity.Bound G rho)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 8*r+2 < p.length)
    (H : G.Subgraph) :
    (H.coe.edgeFinset.card : Real) ≤ (1 + (rho-1)/(r+1)) * Fintype.card H.verts := by
  classical
  exact subgraph_density G rho hrho r hr hminor hgirth H.coe H.hom H.hom_injective

end Paper.HighGirthDilution
#print axioms Paper.HighGirthDilution.minor_induce
#print axioms Paper.HighGirthDilution.girth_induce
#print axioms Paper.HighGirthDilution.density

#print axioms Paper.HighGirthDilution.minor_of_injective
#print axioms Paper.HighGirthDilution.subgraph_density
#print axioms Paper.HighGirthDilution.all_subgraphs
