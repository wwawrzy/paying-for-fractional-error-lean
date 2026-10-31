import Paper.Preliminaries.WeakProjection
import Paper.Preliminaries.StarCounting

/-! Transport actual finite connected subsets into and out of an induced
ambient graph, preserving their physical vertices and cardinality. -/
namespace Paper.InducedSubsets
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def physical (U : Finset V) (S : Finset U) : Finset V := S.image Subtype.val

theorem physical_subset (U : Finset V) (S : Finset U) : physical U S ⊆ U := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact u.property

theorem physical_card (U : Finset V) (S : Finset U) : (physical U S).card = S.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem physical_connected (U : Finset V) (S : Finset U)
    (hconn : ((G.induce (U : Set V)).induce (S : Set U)).Connected) :
    (G.induce (physical U S : Set V)).Connected := by
  classical
  have hc := WeakProjection.connected_image (G.induce (U : Set V)) G (fun x : ↥(U : Set V) => x.val)
    (fun _ _ h => Or.inr h) (S : Set U) hconn
  have he : (fun x : ↥(U : Set V) => x.val) '' (S : Set ↥(U : Set V)) = (physical U S : Set V) := by
    ext v
    simp only [physical, Set.mem_image, Finset.mem_coe, Finset.mem_image]
    rfl
  rwa [he] at hc

noncomputable def lift (U S : Finset V) : Finset U := S.subtype (fun v => v ∈ U)

theorem lift_card (U S : Finset V) (hS : S ⊆ U) : (lift U S).card = S.card :=
  StarCounting.subtype_card U S hS

noncomputable def liftIso (U S : Finset V) (hS : S ⊆ U) :
    G.induce (S : Set V) ≃g (G.induce (U : Set V)).induce (lift U S : Set U) where
  toEquiv := {
    toFun := fun v => ⟨⟨v.val, hS v.property⟩, Finset.mem_subtype.mpr v.property⟩
    invFun := fun v => ⟨v.val.val, Finset.mem_subtype.mp v.property⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  map_rel_iff' := Iff.rfl

theorem lift_connected (U S : Finset V) (hS : S ⊆ U) (hconn : (G.induce (S : Set V)).Connected) :
    ((G.induce (U : Set V)).induce (lift U S : Set U)).Connected :=
  (liftIso G U S hS).connected_iff.mp hconn
end Paper.InducedSubsets
