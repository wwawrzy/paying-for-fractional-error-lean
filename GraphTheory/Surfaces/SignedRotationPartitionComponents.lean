import GraphTheory.Surfaces.SignedRotationComponentClasses
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (r : SignedRotation G) (s : Set V)
variable (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)
include hs in
theorem component_relation_mem_iff {x y : Flag G} (h : r.ComponentRel x y) :
    x.1.fst ∈ s ↔ y.1.fst ∈ s := by
  induction h with
  | rel a b h =>
    rcases h with h | h | h
    · subst b
      exact ⟨fun ha => hs ha a.1.adj, fun hb => hs hb a.1.adj.symm⟩
    · subst b; rfl
    · subst b; rw [r.cornerFlip_source]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

theorem pullFlag_component_relation {x y : Flag G} (h : r.ComponentRel x y)
    (hx : x.1.fst ∈ s) (hy : y.1.fst ∈ s) :
    (r.restrictClosed s hs).ComponentRel (pullFlag s hs x hx) (pullFlag s hs y hy) := by
  induction h with
  | rel a b h =>
    apply Relation.EqvGen.rel
    rcases h with h | h | h
    · left
      apply includeFlag_injective s hs
      rw [r.includeFlag_edgeFlip, include_pullFlag, include_pullFlag, h]
    · right; left
      apply includeFlag_injective s hs
      rw [includeFlag_sideFlip, include_pullFlag, include_pullFlag, h]
    · right; right
      apply includeFlag_injective s hs
      rw [r.includeFlag_cornerFlip, include_pullFlag, include_pullFlag, h]
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ (ih hy hx)
  | trans a b c hab hbc ih hj =>
    have hb := (component_relation_mem_iff r s hs hab).mp hx
    exact Relation.EqvGen.trans _ _ _ (ih hx hb) (hj hb hy)
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (hGH : G ≤ H) (r : SignedRotation G)
include hGH
def partition_componentLabel : r.Component → H.ConnectedComponent :=
  Quotient.lift (fun x => H.connectedComponentMk x.1.fst)
    (fun x y h => ConnectedComponent.sound (((r.component_relation_iff x y).mp h).mono hGH))
def partition_includeComponent (c : H.ConnectedComponent) : (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component → r.Component :=
  Quotient.lift (fun x => Quotient.mk _ (includeFlag c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)) x))
    (fun _ _ h => Quotient.sound (r.includeFlag_component_relation c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)) h))

theorem partition_componentLabel_include (c : H.ConnectedComponent)
    (a : (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component) : partition_componentLabel H hGH r (partition_includeComponent H hGH r c a) = c := by
  induction a using Quotient.inductionOn with
  | _ x => exact x.1.fst.property
def partition_componentClassMap :
    (Σ c : H.ConnectedComponent, (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component) → r.Component :=
  fun z => partition_includeComponent H hGH r z.1 z.2

theorem partition_componentClassMap_injective : Function.Injective (partition_componentClassMap H hGH r) := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have hc := congrArg (partition_componentLabel H hGH r) h
  change partition_componentLabel H hGH r (partition_includeComponent H hGH r c a) =
    partition_componentLabel H hGH r (partition_includeComponent H hGH r d b) at hc
  rw [partition_componentLabel_include H hGH r, partition_componentLabel_include H hGH r] at hc
  subst d
  have hab : a = b := by
    refine Quotient.inductionOn₂ a b (fun x y h => ?_) h
    apply Quotient.sound
    have hp := pullFlag_component_relation r c.supp
      (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))
      (Quotient.exact h) x.1.fst.property y.1.fst.property
    simpa only [pullFlag_include] using hp
  cases hab
  rfl

theorem partition_componentClassMap_surjective : Function.Surjective (partition_componentClassMap H hGH r) := by
  intro a
  induction a using Quotient.inductionOn with
  | _ x =>
    let c := H.connectedComponentMk x.1.fst
    let hs : ∀ ⦃u v⦄, u ∈ c.supp → G.Adj u v → v ∈ c.supp :=
      fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)
    have hx : x.1.fst ∈ c.supp := rfl
    refine ⟨⟨c, Quotient.mk _ (pullFlag c.supp hs x hx)⟩, ?_⟩
    change Quotient.mk _ (includeFlag c.supp hs (pullFlag c.supp hs x hx)) = _
    rw [include_pullFlag]

noncomputable def partition_componentClassEquiv :
    (Σ c : H.ConnectedComponent, (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component) ≃ r.Component :=
  Equiv.ofBijective (partition_componentClassMap H hGH r)
    ⟨partition_componentClassMap_injective H hGH r, partition_componentClassMap_surjective H hGH r⟩

theorem partition_component_card_sum [Fintype H.ConnectedComponent] :
    Nat.card r.Component = ∑ c : H.ConnectedComponent,
      Nat.card (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component := by
  classical
  letI (c : H.ConnectedComponent) : Finite (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Component :=
    inferInstanceAs (Finite (Quotient (Relation.EqvGen.setoid
      (fun a b : Flag (G.induce c.supp) =>
        (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).edgeFlip a = b ∨ sideFlip a = b ∨
          (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).cornerFlip a = b))))
  rw [← Nat.card_congr (partition_componentClassEquiv H hGH r), Nat.card_sigma]

end SimpleGraph.SignedRotation
