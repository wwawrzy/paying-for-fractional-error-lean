import GraphTheory.Surfaces.SignedRotationSmallGenus
import GraphTheory.Surfaces.SignedRotationDeletionFaceCount
namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem added_leaf_sigma (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hu : ∀ w, ¬ G.Adj u w) :
    r.σ (augmentedDart G u v hne (Sum.inr false)) =
      augmentedDart G u v hne (Sum.inr false) := by
  let E := augmentedDartEquiv G u v hne hmiss
  have hs := r.σ_source (augmentedDart G u v hne (Sum.inr false))
  cases ht : E.symm (r.σ (augmentedDart G u v hne (Sum.inr false))) with
  | inl d =>
    have hd := congrArg E ht
    simp only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] at hd
    rw [hd] at hs
    have hdu : d.fst = u := hs
    exact (hu d.snd (by rw [← hdu]; exact d.adj)).elim
  | inr b =>
    have hd := congrArg E ht
    simp only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] at hd
    cases b
    · exact hd
    · rw [hd] at hs
      exact (hne hs.symm).elim

theorem added_leaf_faces_equal (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hu : ∀ w, ¬ G.Adj u w) :
    r.faceOf (augmentedDart G u v hne (Sum.inr false), false) =
      r.faceOf (augmentedDart G u v hne (Sum.inr false), true) := by
  have hs := added_leaf_sigma G u v hne hmiss r hu
  have hc := r.faceOf_cornerFlip (augmentedDart G u v hne (Sum.inr false), false)
  simpa only [cornerFlip, Bool.false_eq_true, ↓reduceIte, hs] using hc.symm
theorem removed_surgery_classes_equal (hne : u ≠ v)
    (r : SignedRotation (G ⊔ edge u v)) (b c : Bool) :
    Quotient.mk (deletionFaceSetoid G u v hne r) (augmentedDart G u v hne (Sum.inr b), c) =
      Quotient.mk (deletionFaceSetoid G u v hne r) (augmentedDart G u v hne (Sum.inr false), false) := by
  have hbase (c : Bool) :
      Quotient.mk (deletionFaceSetoid G u v hne r) (augmentedDart G u v hne (Sum.inr false), c) =
        Quotient.mk (deletionFaceSetoid G u v hne r) (augmentedDart G u v hne (Sum.inr false), false) := by
    cases c
    · rfl
    · apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨false,true,rfl,rfl⟩))
  cases b
  · exact hbase c
  · let j := if r.twist (augmentedDart G u v hne (Sum.inr true)) then c else !c
    have he : Quotient.mk (deletionFaceSetoid G u v hne r)
        (augmentedDart G u v hne (Sum.inr true), c) =
      Quotient.mk (deletionFaceSetoid G u v hne r)
        (augmentedDart G u v hne (Sum.inr false), j) := by
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (Or.inl rfl)
    exact he.trans (hbase j)

theorem deletionFaceMap_surjective_one_end (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v))
    (hret : ∃ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Function.Surjective (deletionFaceMap G u v hne hmiss r) := by
  obtain ⟨b₀,d₀,hd₀⟩ := hret
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨d,c⟩
  let E := augmentedDartEquiv G u v hne hmiss
  cases ht : E.symm d with
  | inl f =>
    have hd : d = augmentedDart G u v hne (Sum.inl f) := by
      have h := congrArg E ht
      simpa only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    subst d
    exact ⟨Quotient.mk _ (f,c), rfl⟩
  | inr b =>
    have hd : d = augmentedDart G u v hne (Sum.inr b) := by
      have h := congrArg E ht
      simpa only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    subst d
    obtain ⟨f,hf⟩ := fresh_corner_survives G u v hne hmiss r b₀ false d₀ hd₀
    refine ⟨Quotient.mk _ (f,true), ?_⟩
    have hc : Quotient.mk (deletionFaceSetoid G u v hne r)
        (augmentedDart G u v hne (Sum.inr b₀), false) =
        Quotient.mk (deletionFaceSetoid G u v hne r) (survivingFlag G u v hne (f,true)) := by
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl hf))
    exact hc.symm.trans ((removed_surgery_classes_equal G u v hne r b₀ false).trans
      (removed_surgery_classes_equal G u v hne r b c).symm)

theorem leaf_deletion_faces_lower (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hu : ∀ w, ¬ G.Adj u w)
    (hret : ∃ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Nat.card r.Face ≤ Nat.card (deleteAddedEdge G u v hne hmiss r).Face := by
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Finite (Quotient (faceMerge G u v hne r)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  letI : Finite (Quotient (deletionFaceSetoid G u v hne r)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  letI : Finite (deleteAddedEdge G u v hne hmiss r).Face :=
    Finite.of_surjective (Quotient.mk _ : Flag G → (deleteAddedEdge G u v hne hmiss r).Face)
      (fun q => Quotient.exists_rep q)
  have he := added_leaf_faces_equal G u v hne hmiss r hu
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
  have h₃ := Nat.card_le_card_of_surjective _
    (deletionFaceMap_surjective_one_end G u v hne hmiss r hret)
  exact h₁.trans (h₂.trans h₃)

theorem leaf_reachable_on_support (hne : u ≠ v) (hu : ∀ w, ¬ G.Adj u w)
    (hH : (G ⊔ edge u v).Connected) (x y : V) (hx : x ∈ G.support) (hy : y ∈ G.support) :
    G.Reachable x y := by
  have hxne : x ≠ u := by
    rintro rfl
    obtain ⟨w,hw⟩ := G.mem_support.mp hx
    exact hu w hw
  have hyne : y ≠ u := by
    rintro rfl
    obtain ⟨w,hw⟩ := G.mem_support.mp hy
    exact hu w hw
  have hleaf (w : V) (hw : (G ⊔ edge u v).Adj u w) : w = v := by
    rcases hw with hw | hw
    · exact (hu w hw).elim
    · have he := (edge_adj u v u w).mp hw
      aesop
  have hp := hH.preconnected.induce_of_degree_eq_one
    (s := {w : V | w ≠ u}) (by
      intro w hw
      have hwu : w = u := by simpa using hw
      subst w
      intro a ha b hb
      exact (hleaf a ha).trans (hleaf b hb).symm)
  have heq : (G ⊔ edge u v).induce {w : V | w ≠ u} = G.induce {w : V | w ≠ u} := by
    ext p q
    change (G.Adj p.val q.val ∨ (edge u v).Adj p.val q.val) ↔ G.Adj p.val q.val
    simp only [edge_adj]
    have hp := p.property
    have hq := q.property
    aesop
  rw [heq] at hp
  exact (hp ⟨x,hxne⟩ ⟨y,hyne⟩).map (SimpleGraph.Embedding.induce (G := G) _).toHom

theorem leaf_deletion_genus_le (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hu : ∀ w, ¬ G.Adj u w)
    (hv : ∃ w, G.Adj v w) (hH : (G ⊔ edge u v).Connected) :
    (deleteAddedEdge G u v hne hmiss r).eulerGenus ≤ r.eulerGenus := by
  classical
  letI : Nontrivial V := ⟨⟨u,v,hne⟩⟩
  obtain ⟨w,hw⟩ := hv
  let d : G.Dart := ⟨(v,w),hw⟩
  letI : Nonempty G.Dart := ⟨d⟩
  letI : Nonempty (G ⊔ edge u v).Dart := ⟨augmentedDart G u v hne (Sum.inl d)⟩
  have hf := leaf_deletion_faces_lower G u v hne hmiss r hu ⟨true,d,rfl⟩
  have hc₁ : Nat.card (deleteAddedEdge G u v hne hmiss r).Component = 1 := by
    let q := deleteAddedEdge G u v hne hmiss r
    letI : Nonempty q.Component := ⟨Quotient.mk _ (d,false)⟩
    letI : Subsingleton q.Component := ⟨by
      intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro x y
      apply Quotient.sound
      apply (q.component_relation_iff x y).mpr
      exact leaf_reachable_on_support G u v hne hu hH _ _
        (G.mem_support.mpr ⟨x.1.snd,x.1.adj⟩)
        (G.mem_support.mpr ⟨y.1.snd,y.1.adj⟩)⟩
    exact Nat.card_unique
  have hc₂ := r.component_card_of_connected hH
  have hs : G.support = {x : V | x ≠ u} := by
    ext x
    constructor
    · intro hx heq
      subst x
      obtain ⟨z,hz⟩ := G.mem_support.mp hx
      exact hu z hz
    · intro hxu
      obtain ⟨z,hz⟩ := hH.preconnected.exists_adj_of_nontrivial x
      rcases hz with hz | hz
      · exact G.mem_support.mpr ⟨z,hz⟩
      · rcases (edge_adj u v x z).mp hz with ⟨hx,hz⟩ | ⟨hx,hz⟩
        · exact (hxu hx).elim
        · subst x
          exact G.mem_support.mpr ⟨w,hw⟩
  have hvc : Nat.card (deleteAddedEdge G u v hne hmiss r).Vertex + 1 = Nat.card r.Vertex := by
    rw [(deleteAddedEdge G u v hne hmiss r).vertex_card, r.vertex_card, hs,
      hH.preconnected.support_eq_univ]
    simp only [Nat.card_eq_fintype_card]
    have hn := Fintype.card_subtype_compl (fun x : V => x = u)
    change Fintype.card {x : V // x ≠ u} = Fintype.card V - 1 at hn
    have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    change Fintype.card {x : V // x ≠ u} + 1 = Fintype.card {x : V // x ∈ (Set.univ : Set V)}
    simp only [Set.mem_univ, Fintype.card_subtype_true]
    omega
  have he := G.card_edgeFinset_sup_edge hmiss hne
  have he₁ := (deleteAddedEdge G u v hne hmiss r).edge_card
  have he₂ := r.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he he₁ he₂
  unfold eulerGenus eulerCharacteristic
  rw [hc₁,hc₂,he₁,he₂,he]
  push_cast
  omega

theorem deletion_genus_le_of_empty (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
    (r : SignedRotation (G ⊔ edge u v)) (hempty : ∀ x y, ¬ G.Adj x y)
    (hH : (G ⊔ edge u v).Connected) :
    (deleteAddedEdge G u v hne hmiss r).eulerGenus ≤ r.eulerGenus := by
  classical
  letI : Nontrivial V := ⟨⟨u,v,hne⟩⟩
  letI : IsEmpty G.Dart := ⟨fun d => hempty d.fst d.snd d.adj⟩
  rw [(deleteAddedEdge G u v hne hmiss r).eulerGenus_eq_zero_of_no_darts]
  apply r.small_connected_genus_nonneg hH
  have hx (x : V) : x = u ∨ x = v := by
    have hs : x ∈ (G ⊔ edge u v).support := by
      rw [hH.preconnected.support_eq_univ]; trivial
    obtain ⟨y,hy⟩ := (G ⊔ edge u v).mem_support.mp hs
    rcases hy with hy | hy
    · exact (hempty x y hy).elim
    · have he := (edge_adj u v x y).mp hy
      aesop
  have hi : (Finset.univ : Finset V) ⊆ {u,v} := by
    intro x _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx x
  have hc : Fintype.card V ≤ ({u,v} : Finset V).card := by
    simpa using Finset.card_le_card hi
  simpa only [Finset.card_pair hne] using hc

end SimpleGraph.SignedRotation





