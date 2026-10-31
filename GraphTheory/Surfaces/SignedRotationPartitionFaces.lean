import GraphTheory.Surfaces.SignedRotationRestrictionFaces
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (hGH : G ≤ H) (r : SignedRotation G)
include hGH
theorem partition_face_relation_component {x y : Flag G}
    (h : (pairSetoid r.edgeFlip r.cornerFlip).r x y) :
    H.connectedComponentMk x.1.fst = H.connectedComponentMk y.1.fst := by
  induction h with
  | rel a b h =>
    rcases h with h | h
    · subst b
      exact ConnectedComponent.connectedComponentMk_eq_of_adj (hGH a.1.adj)
    · subst b
      rw [r.cornerFlip_source]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

def partition_faceComponent : r.Face → H.ConnectedComponent :=
  Quotient.lift (fun x => H.connectedComponentMk x.1.fst)
    (fun _ _ h => partition_face_relation_component H hGH r h)

def partition_componentFaceMap : (Σ c : H.ConnectedComponent, (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Face) → r.Face :=
  fun z => r.includeFace z.1.supp
    (fun {_ _} hu huv => z.1.mem_supp_of_adj_mem_supp hu (hGH huv)) z.2

theorem partition_faceComponent_componentFaceMap (c : H.ConnectedComponent)
    (a : (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Face) :
    partition_faceComponent H hGH r (partition_componentFaceMap H hGH r ⟨c, a⟩) = c := by
  induction a using Quotient.inductionOn with
  | _ x => exact x.1.fst.property

theorem partition_componentFaceMap_injective : Function.Injective (partition_componentFaceMap H hGH r) := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have hc := congrArg (partition_faceComponent H hGH r) h
  rw [partition_faceComponent_componentFaceMap H hGH r, partition_faceComponent_componentFaceMap H hGH r] at hc
  subst d
  have hab : a = b := r.includeFace_injective c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv)) h
  cases hab
  rfl

theorem partition_componentFaceMap_surjective : Function.Surjective (partition_componentFaceMap H hGH r) := by
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

noncomputable def partition_componentFaceEquiv :
    (Σ c : H.ConnectedComponent, (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Face) ≃ r.Face :=
  Equiv.ofBijective (partition_componentFaceMap H hGH r)
    ⟨partition_componentFaceMap_injective H hGH r, partition_componentFaceMap_surjective H hGH r⟩

theorem partition_face_card_sum [Fintype H.ConnectedComponent] :
    Nat.card r.Face = ∑ c : H.ConnectedComponent, Nat.card (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Face := by
  classical
  letI (c : H.ConnectedComponent) : Finite (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).Face :=
    inferInstanceAs (Finite (Quotient (pairSetoid
      (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).edgeFlip (r.restrictClosed c.supp (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).cornerFlip)))
  rw [← Nat.card_congr (partition_componentFaceEquiv H hGH r), Nat.card_sigma]

end SimpleGraph.SignedRotation
