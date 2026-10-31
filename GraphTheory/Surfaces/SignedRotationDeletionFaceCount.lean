import GraphTheory.Surfaces.FaceMergeCard
import GraphTheory.Surfaces.SignedRotationDeletionFaceMap
import GraphTheory.Surfaces.SignedRotationEulerBound

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v)
def faceMerge (r : SignedRotation (G ⊔ edge u v)) : Setoid r.Face :=
  Paper.FaceSurgery.mergeTwo
    (r.faceOf (augmentedDart G u v hne (Sum.inr false), false))
    (r.faceOf (augmentedDart G u v hne (Sum.inr false), true))

theorem surgery_respects_merge (r : SignedRotation (G ⊔ edge u v))
    {x y : Flag (G ⊔ edge u v)} (h : (deletionFaceSetoid G u v hne r).r x y) :
    (Quotient.mk (faceMerge G u v hne r) (r.faceOf x)) =
      Quotient.mk (faceMerge G u v hne r) (r.faceOf y) := by
  induction h with
  | rel a b h =>
    rcases h with h | h | ⟨d,c,rfl,rfl⟩
    · subst b; simp
    · subst b; simp
    · apply Quotient.sound
      right
      exact ⟨removed_flag_faces G u v hne r d c, removed_flag_faces G u v hne r d (!c)⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

def surgeryToMerge (r : SignedRotation (G ⊔ edge u v)) :
    Quotient (deletionFaceSetoid G u v hne r) → Quotient (faceMerge G u v hne r) :=
  Quotient.lift (fun x => Quotient.mk _ (r.faceOf x))
    (fun _ _ h => surgery_respects_merge G u v hne r h)

theorem surgeryToMerge_surjective (r : SignedRotation (G ⊔ edge u v)) :
    Function.Surjective (surgeryToMerge G u v hne r) := by
  intro z
  refine Quotient.inductionOn z ?_
  intro f
  refine Quotient.inductionOn f ?_
  intro x
  exact ⟨Quotient.mk _ x, rfl⟩

theorem old_faces_le_surgery_add_one (r : SignedRotation (G ⊔ edge u v)) :
    Nat.card r.Face ≤ Nat.card (Quotient (deletionFaceSetoid G u v hne r)) + 1 := by
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Finite (Quotient (deletionFaceSetoid G u v hne r)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  have hm := Paper.FaceSurgery.mergeTwo_card
    (r.faceOf (augmentedDart G u v hne (Sum.inr false), false))
    (r.faceOf (augmentedDart G u v hne (Sum.inr false), true))
  have hs := Nat.card_le_card_of_surjective _ (surgeryToMerge_surjective G u v hne r)
  change Nat.card (Quotient (faceMerge G u v hne r)) ≤ _ at hs
  change Nat.card r.Face ≤ Nat.card (Quotient (faceMerge G u v hne r)) + 1 at hm
  omega
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem deletion_faces_lower (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v))
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Nat.card r.Face ≤ Nat.card (deleteAddedEdge G u v hne hmiss r).Face + 1 := by
  have h₁ := old_faces_le_surgery_add_one G u v hne r
  have h₂ := deletion_surgery_classes_le_faces G u v hne hmiss r hends
  omega
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem deletion_genus_le_of_connected (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hG : G.Connected) :
    (deleteAddedEdge G u v hne hmiss r).eulerGenus ≤ r.eulerGenus := by
  classical
  letI : Nontrivial V := ⟨⟨u,v,hne⟩⟩
  have hOld : (G ⊔ edge u v).Connected := hG.mono le_sup_left
  have hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst := by
    intro b
    let w := (augmentedDart G u v hne (Sum.inr b)).fst
    have hw : w ∈ G.support := by rw [hG.preconnected.support_eq_univ]; trivial
    obtain ⟨z,hz⟩ := G.mem_support.mp hw
    exact ⟨⟨(w,z),hz⟩,rfl⟩
  obtain ⟨d,hd⟩ := hends false
  letI : Nonempty G.Dart := ⟨d⟩
  letI : Nonempty (G ⊔ edge u v).Dart := ⟨augmentedDart G u v hne (Sum.inl d)⟩
  have hf := deletion_faces_lower G u v hne hmiss r hends
  have hc₁ := (deleteAddedEdge G u v hne hmiss r).component_card_of_connected hG
  have hc₂ := r.component_card_of_connected hOld
  have hv₁ := (deleteAddedEdge G u v hne hmiss r).vertex_card
  have hv₂ := r.vertex_card
  rw [hG.preconnected.support_eq_univ] at hv₁
  rw [hOld.preconnected.support_eq_univ] at hv₂
  have he := G.card_edgeFinset_sup_edge hmiss hne
  have he₁ := (deleteAddedEdge G u v hne hmiss r).edge_card
  have he₂ := r.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he he₁ he₂
  unfold eulerGenus eulerCharacteristic
  rw [hc₁, hc₂, hv₁, hv₂, he₁, he₂, he]
  push_cast
  omega
end SimpleGraph.SignedRotation
