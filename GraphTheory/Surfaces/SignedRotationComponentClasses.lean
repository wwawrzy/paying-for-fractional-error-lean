import GraphTheory.Surfaces.SignedRotationComponentVertices
import GraphTheory.Surfaces.SignedRotationComponents

/-! Flag components decompose over graph components, including isolated vertices
whose induced graphs have no flags and contribute no flag components. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G)

def componentLabel : r.Component → G.ConnectedComponent :=
  Quotient.lift (fun x => G.connectedComponentMk x.1.fst)
    (fun x y h => ConnectedComponent.sound ((r.component_relation_iff x y).mp h))

theorem includeFlag_component_relation (s : Set V)
    (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)
    {x y : Flag (G.induce s)}
    (h : (r.restrictClosed s hs).ComponentRel x y) :
    r.ComponentRel (includeFlag s hs x) (includeFlag s hs y) := by
  induction h with
  | rel a b h =>
    apply Relation.EqvGen.rel
    rcases h with h | h | h
    · left
      rw [← r.includeFlag_edgeFlip, h]
    · right; left
      rw [← includeFlag_sideFlip, h]
    · right; right
      rw [← r.includeFlag_cornerFlip, h]
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih hj => exact Relation.EqvGen.trans _ _ _ ih hj

def includeComponent (c : G.ConnectedComponent) : (r.restrictComponent c).Component → r.Component :=
  Quotient.lift (fun x => Quotient.mk _ (includeFlag c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv) x))
    (fun _ _ h => Quotient.sound (r.includeFlag_component_relation c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv) h))

theorem componentLabel_include (c : G.ConnectedComponent)
    (a : (r.restrictComponent c).Component) : r.componentLabel (r.includeComponent c a) = c := by
  induction a using Quotient.inductionOn with
  | _ x => exact x.1.fst.property

theorem restricted_component_subsingleton (c : G.ConnectedComponent) :
    Subsingleton (r.restrictComponent c).Component := by
  classical
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (((r.restrictComponent c).component_relation_iff x y).mpr
    (c.connected_toSimpleGraph.preconnected _ _))

def componentClassMap :
    (Σ c : G.ConnectedComponent, (r.restrictComponent c).Component) → r.Component :=
  fun z => r.includeComponent z.1 z.2

theorem componentClassMap_injective : Function.Injective r.componentClassMap := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have hc := congrArg r.componentLabel h
  change r.componentLabel (r.includeComponent c a) =
    r.componentLabel (r.includeComponent d b) at hc
  rw [r.componentLabel_include, r.componentLabel_include] at hc
  subst d
  have hab : a = b := (r.restricted_component_subsingleton c).elim a b
  cases hab
  rfl

theorem componentClassMap_surjective : Function.Surjective r.componentClassMap := by
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

noncomputable def componentClassEquiv :
    (Σ c : G.ConnectedComponent, (r.restrictComponent c).Component) ≃ r.Component :=
  Equiv.ofBijective r.componentClassMap
    ⟨r.componentClassMap_injective, r.componentClassMap_surjective⟩

theorem component_card_sum [Fintype G.ConnectedComponent] :
    Nat.card r.Component = ∑ c : G.ConnectedComponent,
      Nat.card (r.restrictComponent c).Component := by
  classical
  letI (c : G.ConnectedComponent) : Finite (r.restrictComponent c).Component :=
    inferInstanceAs (Finite (Quotient (Relation.EqvGen.setoid
      (fun a b : Flag (G.induce c.supp) =>
        (r.restrictComponent c).edgeFlip a = b ∨ sideFlip a = b ∨
          (r.restrictComponent c).cornerFlip a = b))))
  rw [← Nat.card_congr r.componentClassEquiv, Nat.card_sigma]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.componentClassEquiv
#print axioms SimpleGraph.SignedRotation.component_card_sum
