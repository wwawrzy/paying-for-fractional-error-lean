import GraphTheory.Surfaces.SignedRotationLeafDeletion
import GraphTheory.Surfaces.SignedRotationDeletionFaceCount
import GraphTheory.Surfaces.SignedRotationFaceFlags
import Mathlib.Tactic
namespace Paper.FaceSurgery
variable {X : Type*}
theorem even_card_involution (f : X → X) (hf : Function.Involutive f)
    (s : Finset X) (hclosed : ∀ x ∈ s, f x ∈ s) (hne : ∀ x ∈ s, f x ≠ x) :
    Even s.card := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs : s.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have hfa := hclosed a ha
    have hneq := hne a ha
    let t := (s.erase a).erase (f a)
    have ht : t ⊂ s := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
      intro heq
      have hat : a ∈ t := heq.symm ▸ ha
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hat).2).1 rfl
    have htc : ∀ x ∈ t, f x ∈ t := by
      intro x hx
      obtain ⟨hxf,hxa,hxs⟩ := by simpa only [t, Finset.mem_erase] using hx
      have hfna : f x ≠ a := by
        intro h
        have hh := congrArg f h
        rw [hf x] at hh
        exact hxf hh
      have hfnf : f x ≠ f a := fun h => hxa (hf.injective h)
      simp only [t, Finset.mem_erase]
      exact ⟨hfnf,hfna,hclosed x hxs⟩
    have htn : ∀ x ∈ t, f x ≠ x := fun x hx => hne x (ht.subset hx)
    obtain ⟨k,hk⟩ := ih t ht htc htn
    have hcount : t.card + 2 = s.card := by
      have hfa' : f a ∈ s.erase a := Finset.mem_erase.mpr ⟨hneq,hfa⟩
      dsimp only [t]
      rw [Finset.card_erase_of_mem hfa', Finset.card_erase_of_mem ha]
      have hc : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨a,ha,f a,hfa,hneq.symm⟩
      omega
    exact ⟨k+1, by omega⟩
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
theorem even_crossing_card [DecidableEq X] (f g : X → X) (hf : Function.Involutive f)
    (hg : Function.Involutive g) (s : Finset X)
    (hfne : ∀ x ∈ s, f x ≠ x) (hgne : ∀ x ∈ s, g x ≠ x)
    (hgclosed : ∀ x ∈ s, g x ∈ s) :
    Even (s.filter (fun x => f x ∉ s)).card := by
  classical
  have hs := even_card_involution g hg s hgclosed hgne
  let t := s.filter (fun x => f x ∈ s)
  have htclosed : ∀ x ∈ t, f x ∈ t := by
    intro x hx
    obtain ⟨hx,hfx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hfx, by simpa only [hf x] using hx⟩
  have ht := even_card_involution f hf t htclosed
    (fun x hx => hfne x (Finset.mem_filter.mp hx).1)
  have hsum : t.card + (s.filter (fun x => f x ∉ s)).card = s.card := by
    exact Finset.card_filter_add_card_filter_not (s := s) (fun x => f x ∈ s)
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := ht
  refine ⟨a-b, ?_⟩
  omega

end Paper.FaceSurgery


namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)
attribute [local instance] Classical.propDecidable Classical.decEq
theorem face_cut_even (S : Set V) (q : r.Face) :
    Even (Finset.univ.filter (fun x : Flag G => r.faceOf x = q ∧
      x.1.fst ∈ S ∧ x.1.snd ∉ S)).card := by
  let s := Finset.univ.filter (fun x : Flag G => r.faceOf x = q ∧ x.1.fst ∈ S)
  have hc : ∀ x ∈ s, r.cornerFlip x ∈ s := by
    intro x hx
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and,
      r.faceOf_cornerFlip, r.cornerFlip_source] using hx
  have hp := Paper.FaceSurgery.even_crossing_card r.edgeFlip r.cornerFlip
    r.edgeFlip_involutive r.cornerFlip_involutive s
    (fun x _ => r.edgeFlip_ne_self x) (fun x _ => r.cornerFlip_ne_self x) hc
  have he : s.filter (fun x => r.edgeFlip x ∉ s) =
      Finset.univ.filter (fun x : Flag G => r.faceOf x = q ∧
        x.1.fst ∈ S ∧ x.1.snd ∉ S) := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, r.faceOf_edgeFlip]
    change ((r.faceOf x = q ∧ x.1.fst ∈ S) ∧ ¬ (r.faceOf x = q ∧ x.1.snd ∈ S)) ↔ _
    tauto
  rwa [he] at hp
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem bridge_cut_faces_equal (hne : u ≠ v) (r : SignedRotation (G ⊔ edge u v))
    (S : Set V) (hu : u ∈ S) (hv : v ∉ S)
    (hclosed : ∀ ⦃x y⦄, x ∈ S → G.Adj x y → y ∈ S) :
    r.faceOf (augmentedDart G u v hne (Sum.inr false), false) =
      r.faceOf (augmentedDart G u v hne (Sum.inr false), true) := by
  classical
  by_contra hneq
  let d₀ := augmentedDart G u v hne (Sum.inr false)
  let q := r.faceOf (d₀,false)
  have hd (d : (G ⊔ edge u v).Dart) (hs : d.fst ∈ S) (ht : d.snd ∉ S) : d = d₀ := by
    rcases d.adj with h | h
    · exact (ht (hclosed hs h)).elim
    · rcases (edge_adj u v d.fst d.snd).mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Dart.ext _ _ (Prod.ext h₁ h₂)
      · exact (hv (h₁ ▸ hs)).elim
  have he : Finset.univ.filter (fun x : Flag (G ⊔ edge u v) =>
      r.faceOf x = q ∧ x.1.fst ∈ S ∧ x.1.snd ∉ S) = {(d₀,false)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hx,hs,ht⟩
      rcases x with ⟨d,c⟩
      have hdd := hd d hs ht
      subst d
      cases c
      · rfl
      · exact (hneq hx.symm).elim
    · rintro rfl
      exact ⟨rfl,hu,hv⟩
  have hp := r.face_cut_even S q
  rw [he, Finset.card_singleton] at hp
  norm_num at hp
end SimpleGraph.SignedRotation
namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem bridge_faces_equal (hne : u ≠ v) (r : SignedRotation (G ⊔ edge u v))
    (hsep : ¬ G.Reachable u v) :
    r.faceOf (augmentedDart G u v hne (Sum.inr false), false) =
      r.faceOf (augmentedDart G u v hne (Sum.inr false), true) := by
  exact bridge_cut_faces_equal G u v hne r {x | G.Reachable u x}
    (Reachable.refl u) hsep (by intro x y hx hxy; exact hx.trans hxy.reachable)
end SimpleGraph.SignedRotation

namespace Paper.FaceSurgery
variable {X Y : Type*}
theorem card_add_one_le_of_collision [Finite X] [Finite Y]
    (f : X → Y) (hs : Function.Surjective f) (a b : X) (hab : a ≠ b)
    (heq : f a = f b) : Nat.card Y + 1 ≤ Nat.card X := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hr : Function.Surjective (fun x : {x : X // x ≠ a} => f x.val) := by
    intro y
    obtain ⟨x,hx⟩ := hs y
    by_cases hxa : x = a
    · subst x
      exact ⟨⟨b,hab.symm⟩, heq.symm.trans hx⟩
    · exact ⟨⟨x,hxa⟩,hx⟩
  have hc := Nat.card_le_card_of_surjective _ hr
  have hn : Nat.card {x : X // x ≠ a} + 1 = Nat.card X := by
    simp only [Nat.card_eq_fintype_card]
    have hsum := Fintype.card_subtype_compl (fun x : X => x = a)
    change Fintype.card {x : X // x ≠ a} = Fintype.card X - 1 at hsum
    have hp : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨a⟩
    omega
  omega
end Paper.FaceSurgery

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem bridge_face_map_collision (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hsep : ¬ G.Reachable u v)
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    ∃ a b : (deleteAddedEdge G u v hne hmiss r).Face,
      a ≠ b ∧ deletionFaceMap G u v hne hmiss r a = deletionFaceMap G u v hne hmiss r b := by
  obtain ⟨du,hdu⟩ := hends false
  obtain ⟨dv,hdv⟩ := hends true
  obtain ⟨fu,hfu⟩ := fresh_corner_survives G u v hne hmiss r false false du hdu
  obtain ⟨fv,hfv⟩ := fresh_corner_survives G u v hne hmiss r true false dv hdv
  have hsu : fu.fst = u := by
    have h := congrArg (fun z : Flag (G ⊔ edge u v) => z.1.fst) hfu
    dsimp only at h
    rw [r.cornerFlip_source] at h
    exact h.symm
  have hsv : fv.fst = v := by
    have h := congrArg (fun z : Flag (G ⊔ edge u v) => z.1.fst) hfv
    dsimp only at h
    rw [r.cornerFlip_source] at h
    exact h.symm
  let q := deleteAddedEdge G u v hne hmiss r
  refine ⟨Quotient.mk _ (fu,true),Quotient.mk _ (fv,true),?_,?_⟩
  · intro he
    have hr := Quotient.exact he
    have hc : q.ComponentRel (fu,true) (fv,true) :=
      Relation.EqvGen.mono (fun _ _ h => h.elim Or.inl (fun h => Or.inr (Or.inr h))) hr
    have hp := (q.component_relation_iff (fu,true) (fv,true)).mp hc
    exact hsep (by simpa only [hsu,hsv] using hp)
  · have hu : Quotient.mk (deletionFaceSetoid G u v hne r)
        (augmentedDart G u v hne (Sum.inr false), false) =
        Quotient.mk (deletionFaceSetoid G u v hne r) (survivingFlag G u v hne (fu,true)) := by
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl hfu))
    have hv : Quotient.mk (deletionFaceSetoid G u v hne r)
        (augmentedDart G u v hne (Sum.inr true), false) =
        Quotient.mk (deletionFaceSetoid G u v hne r) (survivingFlag G u v hne (fv,true)) := by
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl hfv))
    exact hu.symm.trans ((removed_surgery_classes_equal G u v hne r true false).symm.trans hv)
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem bridge_deletion_faces_lower (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hsep : ¬ G.Reachable u v)
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Nat.card r.Face + 1 ≤ Nat.card (deleteAddedEdge G u v hne hmiss r).Face := by
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Finite (Quotient (faceMerge G u v hne r)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  letI : Finite (Quotient (deletionFaceSetoid G u v hne r)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  letI : Finite (deleteAddedEdge G u v hne hmiss r).Face :=
    Finite.of_surjective (Quotient.mk _ : Flag G → (deleteAddedEdge G u v hne hmiss r).Face)
      (fun q => Quotient.exists_rep q)
  have he := bridge_faces_equal G u v hne r hsep
  have hi : Function.Injective (Quotient.mk (faceMerge G u v hne r)) := by
    intro x y h
    have hr := Quotient.exact h
    change x = y ∨
      (x = r.faceOf (augmentedDart G u v hne (Sum.inr false), false) ∨
       x = r.faceOf (augmentedDart G u v hne (Sum.inr false), true)) ∧
      (y = r.faceOf (augmentedDart G u v hne (Sum.inr false), false) ∨
       y = r.faceOf (augmentedDart G u v hne (Sum.inr false), true)) at hr
    rcases hr with hr | ⟨hx,hy⟩
    · exact hr
    · rw [he] at hx hy
      exact (hx.elim id id).trans (hy.elim id id).symm
  have h₁ := Nat.card_le_card_of_injective _ hi
  have h₂ := Nat.card_le_card_of_surjective _ (surgeryToMerge_surjective G u v hne r)
  obtain ⟨a,b,hab,heq⟩ := bridge_face_map_collision G u v hne hmiss r hsep hends
  have h₃ := Paper.FaceSurgery.card_add_one_le_of_collision
    (deletionFaceMap G u v hne hmiss r)
    (deletionFaceMap_surjective G u v hne hmiss r hends) a b hab heq
  omega
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem reachable_endpoint_cases (hH : (G ⊔ edge u v).Connected) (x : V) :
    G.Reachable u x ∨ G.Reachable v x := by
  have hw {a b : V} (p : (G ⊔ edge u v).Walk a b) :
      G.Reachable u a ∨ G.Reachable v a → G.Reachable u b ∨ G.Reachable v b := by
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      intro ha
      apply ih
      rcases hab with hab | hab
      · exact ha.elim (fun h => Or.inl (h.trans hab.reachable))
          (fun h => Or.inr (h.trans hab.reachable))
      · rcases (edge_adj u v a b).mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact Or.inr (by rw [hb])
        · exact Or.inl (by rw [hb])
  obtain ⟨p⟩ := hH.preconnected u x
  exact hw p (Or.inl (Reachable.refl u))

theorem deletion_component_card_le_two (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hH : (G ⊔ edge u v).Connected)
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Nat.card (deleteAddedEdge G u v hne hmiss r).Component ≤ 2 := by
  obtain ⟨du,hdu⟩ := hends false
  obtain ⟨dv,hdv⟩ := hends true
  let q := deleteAddedEdge G u v hne hmiss r
  let f : Bool → q.Component := fun b => if b then Quotient.mk _ (dv,false) else Quotient.mk _ (du,false)
  have hf : Function.Surjective f := by
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    rcases reachable_endpoint_cases G u v hH x.1.fst with hu | hv
    · refine ⟨false, ?_⟩
      apply Quotient.sound
      apply (q.component_relation_iff (du,false) x).mpr
      simpa only [← hdu] using hu
    · refine ⟨true, ?_⟩
      apply Quotient.sound
      apply (q.component_relation_iff (dv,false) x).mpr
      simpa only [← hdv] using hv
  simpa using Nat.card_le_card_of_surjective f hf
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
theorem bridge_deletion_genus_le (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hH : (G ⊔ edge u v).Connected)
    (hsep : ¬ G.Reachable u v)
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    (deleteAddedEdge G u v hne hmiss r).eulerGenus ≤ r.eulerGenus := by
  classical
  obtain ⟨du,hdu⟩ := hends false
  obtain ⟨dv,hdv⟩ := hends true
  letI : Nonempty (G ⊔ edge u v).Dart := ⟨augmentedDart G u v hne (Sum.inl du)⟩
  have hf := bridge_deletion_faces_lower G u v hne hmiss r hsep hends
  have hc₁ := deletion_component_card_le_two G u v hne hmiss r hH hends
  have hc₂ := r.component_card_of_connected hH
  have hs : (G ⊔ edge u v).support = G.support := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (G ⊔ edge u v).mem_support.mp hx
      rcases hy with hy | hy
      · exact G.mem_support.mpr ⟨y,hy⟩
      · rcases (edge_adj u v x y).mp hy with ⟨hx,hy⟩ | ⟨hx,hy⟩
        · have hd : du.fst = u := hdu.symm
          rw [hx, ← hd]
          exact G.mem_support.mpr ⟨du.snd,du.adj⟩
        · have hd : dv.fst = v := hdv.symm
          rw [hx, ← hd]
          exact G.mem_support.mpr ⟨dv.snd,dv.adj⟩
    · rintro ⟨y,hy⟩
      exact (G ⊔ edge u v).mem_support.mpr ⟨y,Or.inl hy⟩
  have hv₁ := (deleteAddedEdge G u v hne hmiss r).vertex_card
  have hv₂ := r.vertex_card
  rw [hs] at hv₂
  have he := G.card_edgeFinset_sup_edge hmiss hne
  have he₁ := (deleteAddedEdge G u v hne hmiss r).edge_card
  have he₂ := r.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he he₁ he₂
  unfold eulerGenus eulerCharacteristic
  rw [hc₂,hv₁,hv₂,he₁,he₂,he]
  push_cast
  omega
end SimpleGraph.SignedRotation
