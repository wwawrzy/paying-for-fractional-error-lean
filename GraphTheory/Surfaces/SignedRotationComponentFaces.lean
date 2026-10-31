import GraphTheory.Surfaces.SignedRotationRestrictionFaces

/-! Faces decompose exactly over graph connected components. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G)

theorem face_relation_component {x y : Flag G}
    (h : (pairSetoid r.edgeFlip r.cornerFlip).r x y) :
    G.connectedComponentMk x.1.fst = G.connectedComponentMk y.1.fst := by
  induction h with
  | rel a b h =>
    rcases h with h | h
    · subst b
      exact ConnectedComponent.connectedComponentMk_eq_of_adj a.1.adj
    · subst b
      rw [r.cornerFlip_source]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

def faceComponent : r.Face → G.ConnectedComponent :=
  Quotient.lift (fun x => G.connectedComponentMk x.1.fst)
    (fun _ _ h => r.face_relation_component h)

def componentFaceMap : (Σ c : G.ConnectedComponent, (r.restrictComponent c).Face) → r.Face :=
  fun z => r.includeFace z.1.supp
    (fun {_ _} hu huv => z.1.mem_supp_of_adj_mem_supp hu huv) z.2

theorem faceComponent_componentFaceMap (c : G.ConnectedComponent)
    (a : (r.restrictComponent c).Face) :
    r.faceComponent (r.componentFaceMap ⟨c, a⟩) = c := by
  induction a using Quotient.inductionOn with
  | _ x => exact x.1.fst.property

theorem componentFaceMap_injective : Function.Injective r.componentFaceMap := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have hc := congrArg r.faceComponent h
  rw [r.faceComponent_componentFaceMap, r.faceComponent_componentFaceMap] at hc
  subst d
  have hab : a = b := r.includeFace_injective c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv) h
  cases hab
  rfl

theorem componentFaceMap_surjective : Function.Surjective r.componentFaceMap := by
  intro a
  induction a using Quotient.inductionOn with
  | _ x =>
    let c := G.connectedComponentMk x.1.fst
    let hs : ∀ ⦃u v⦄, u ∈ c.supp → G.Adj u v → v ∈ c.supp :=
      fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv
    have hx : x.1.fst ∈ c.supp := rfl
    refine ⟨⟨c, Quotient.mk _ (pullFlag c.supp hs x hx)⟩, ?_⟩
    change Quotient.mk _ (includeFlag c.supp hs (pullFlag c.supp hs x hx)) = _
    rw [include_pullFlag]

noncomputable def componentFaceEquiv :
    (Σ c : G.ConnectedComponent, (r.restrictComponent c).Face) ≃ r.Face :=
  Equiv.ofBijective r.componentFaceMap
    ⟨r.componentFaceMap_injective, r.componentFaceMap_surjective⟩

theorem face_card_sum [Fintype G.ConnectedComponent] :
    Nat.card r.Face = ∑ c : G.ConnectedComponent, Nat.card (r.restrictComponent c).Face := by
  classical
  letI (c : G.ConnectedComponent) : Finite (r.restrictComponent c).Face :=
    inferInstanceAs (Finite (Quotient (pairSetoid
      (r.restrictComponent c).edgeFlip (r.restrictComponent c).cornerFlip)))
  rw [← Nat.card_congr r.componentFaceEquiv, Nat.card_sigma]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.componentFaceMap_injective
#print axioms SimpleGraph.SignedRotation.componentFaceMap_surjective
#print axioms SimpleGraph.SignedRotation.componentFaceEquiv
#print axioms SimpleGraph.SignedRotation.face_card_sum
