import GraphTheory.Surfaces.SignedRotationContractRotation
import GraphTheory.Surfaces.SignedRotationComponents
import GraphTheory.Surfaces.SignedRotationEdges
import GraphTheory.Surfaces.SignedRotationSubgraphGenus
import GraphTheory.Surfaces.SignedRotationSwitch
namespace SimpleGraph.SignedRotation
open Equiv Equiv.Perm PlaneTopology.PlanePermutationDeletion
variable {A Q : Type*} [DecidableEq A]
theorem erasePoint_corner_label (p : Perm A) (a : A) (L : A × Bool → Q)
    (hp : ∀ x, L (x,false) = L (p x,true))
    (ha : L (a,false) = L (a,true)) (x : A) :
    L (x,false) = L (erasePoint p a x,true) := by
  by_cases hx : x = a
  · subst x
    rw [erasePoint_fixed]
    exact ha
  · by_cases hpx : p x = a
    · rw [erasePoint_apply_of_eq p a x hpx]
      exact (hp x).trans ((congrArg (fun z => L (z,true)) hpx).trans (ha.symm.trans (hp a)))
    · rw [erasePoint_apply_of_ne p a x hx hpx]
      exact hp x

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] (r : SignedRotation G) (d : G.Dart)
def contractionFaceLabel (x : G.Dart × Bool) : r.Face :=
  Quotient.mk _ (x.1, if x.1 = d ∨ x.1 = d.symm then false else x.2)

theorem old_corner_label (x : G.Dart) :
    (Quotient.mk _ (x,false) : r.Face) = Quotient.mk _ (r.σ x,true) := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact Or.inr rfl

theorem old_cross_label (ht : r.twist d = false) :
    (Quotient.mk _ (d,true) : r.Face) = Quotient.mk _ (d.symm,false) := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  apply Or.inl
  simp [edgeFlip,ht]

theorem contractionFaceLabel_removed (b : Bool) :
    r.contractionFaceLabel d (d,b) = r.contractionFaceLabel d (d,false) := by
  simp [contractionFaceLabel]

theorem contractionFaceLabel_reverse_removed (b : Bool) :
    r.contractionFaceLabel d (d.symm,b) = r.contractionFaceLabel d (d.symm,false) := by
  simp [contractionFaceLabel]

theorem contractionSplice_face_label (ht : r.twist d = false) (x : G.Dart) :
    r.contractionFaceLabel d (x,false) =
      r.contractionFaceLabel d (r.contractionSplice d x,true) := by
  have hh := r.old_corner_label x
  by_cases h₁ : r.σ x = d
  · have he := r.old_cross_label d ht
    rw [h₁] at hh
    simpa [contractionFaceLabel,contractionSplice,mul_apply,h₁] using hh.trans he
  · by_cases h₂ : r.σ x = d.symm
    · have he := r.old_cross_label d.symm (by simpa only [r.twist_symm] using ht)
      rw [h₂] at hh
      simpa [contractionFaceLabel,contractionSplice,mul_apply,h₂] using hh.trans he
    · simpa [contractionFaceLabel,contractionSplice,mul_apply,
        Equiv.swap_apply_of_ne_of_ne h₁ h₂,h₁,h₂] using hh

theorem contractionErased_face_label (ht : r.twist d = false) (x : G.Dart) :
    r.contractionFaceLabel d (x,false) =
      r.contractionFaceLabel d (r.contractionErased d x,true) := by
  apply erasePoint_corner_label
  · intro z
    apply erasePoint_corner_label
    · exact r.contractionSplice_face_label d ht
    · exact (r.contractionFaceLabel_reverse_removed d true).symm
  · exact (r.contractionFaceLabel_removed d true).symm

theorem contractionDart_face_label (ht : r.twist d = false) (x : ContractionDart d) :
    (Quotient.mk _ (x.val,false) : r.Face) =
      Quotient.mk _ ((r.contractionDartPerm d x).val,true) := by
  have h := r.contractionErased_face_label d ht x.val
  have hx := (r.contractionErased_survives d x.val).mpr x.property
  simpa only [contractionFaceLabel, if_neg (not_or.mpr x.property),
    if_neg (not_or.mpr hx)] using h

variable (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w))
noncomputable def contractPullFlag (x : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd)) : Flag G :=
  (((contractionDartEquiv d hc).symm x.1).val,x.2)
noncomputable def contractFaceLabel (x : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd)) : r.Face :=
  Quotient.mk _ (contractPullFlag d hc x)

theorem contractFaceLabel_forward (ht : r.twist d = false)
    (x : (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd).Dart) :
    r.contractFaceLabel d hc (x,false) =
      r.contractFaceLabel d hc ((r.contractRotation d hc).σ x,true) := by
  let e := contractionDartEquiv d hc
  change (Quotient.mk _ ((e.symm x).val,false) : r.Face) =
    Quotient.mk _ ((e.symm (e (r.contractionDartPerm d (e.symm x)))).val,true)
  rw [e.symm_apply_apply]
  exact r.contractionDart_face_label d ht _

theorem contractFaceLabel_corner (ht : r.twist d = false)
    (x : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd)) :
    r.contractFaceLabel d hc x =
      r.contractFaceLabel d hc ((r.contractRotation d hc).cornerFlip x) := by
  rcases x with ⟨x,b⟩
  cases b
  · exact r.contractFaceLabel_forward d hc ht x
  · have h := r.contractFaceLabel_forward d hc ht ((r.contractRotation d hc).σ.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

theorem contractPullFlag_edge
    (x : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd)) :
    contractPullFlag d hc ((r.contractRotation d hc).edgeFlip x) =
      r.edgeFlip (contractPullFlag d hc x) := by
  let e := contractionDartEquiv d hc
  have he (a : (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd).Dart) :
      e.symm a.symm = contractionDartReverse d (e.symm a) := by
    apply e.injective
    change e (e.symm a.symm) = contractionDartMap d (contractionDartReverse d (e.symm a))
    rw [e.apply_symm_apply, contractionDartMap_reverse]
    change a.symm = (e (e.symm a)).symm
    rw [e.apply_symm_apply]
  rcases x with ⟨x,b⟩
  change ((e.symm x.symm).val, if r.twist (e.symm x).val then b else !b) = _
  rw [he]
  rfl

theorem contractFaceLabel_edge
    (x : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd)) :
    r.contractFaceLabel d hc x =
      r.contractFaceLabel d hc ((r.contractRotation d hc).edgeFlip x) := by
  unfold contractFaceLabel
  rw [r.contractPullFlag_edge d hc]
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl rfl)

noncomputable def contractFaceMap (ht : r.twist d = false) : (r.contractRotation d hc).Face → r.Face :=
  Quotient.lift (r.contractFaceLabel d hc) (by
    intro x y h
    induction h with
    | rel x y h =>
      rcases h with h | h
      · subst y; exact r.contractFaceLabel_edge d hc x
      · subst y; exact r.contractFaceLabel_corner d hc ht x
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem contractFaceMap_mk (ht : r.twist d = false) (x : ContractionDart d) (b : Bool) :
    r.contractFaceMap d hc ht (Quotient.mk _ (contractionDartEquiv d hc x,b)) =
      (Quotient.mk _ (x.val,b) : r.Face) := by
  change (Quotient.mk _ (((contractionDartEquiv d hc).symm (contractionDartEquiv d hc x)).val,b) : r.Face) = _
  rw [Equiv.symm_apply_apply]

theorem contractFaceMap_surjective_of_nonfixed (ht : r.twist d = false)
    (hd : r.σ d ≠ d) : Function.Surjective (r.contractFaceMap d hc ht) := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  have hs : r.σ d ≠ d.symm := by
    intro he
    have hh := r.σ_source d
    rw [he] at hh
    exact hne hh.symm
  have hr (x : ContractionDart d) (b : Bool) :
      ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (x.val,b) : r.Face) :=
    ⟨Quotient.mk _ (contractionDartEquiv d hc x,b),r.contractFaceMap_mk d hc ht x b⟩
  have hdf : ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (d,false) : r.Face) := by
    obtain ⟨q,hq⟩ := hr ⟨r.σ d,hd,hs⟩ true
    exact ⟨q,hq.trans (r.old_corner_label d).symm⟩
  have hxrev := r.old_cross_label d.symm (by simpa only [r.twist_symm] using ht)
  have hdrf : ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (d.symm,false) : r.Face) := by
    by_cases hfix : r.σ d.symm = d.symm
    · obtain ⟨q,hq⟩ := hdf
      have hh := r.old_corner_label d.symm
      rw [hfix] at hh
      exact ⟨q,hq.trans (hh.trans hxrev).symm⟩
    · have hs' : r.σ d.symm ≠ d := by
        intro he
        have hh := r.σ_source d.symm
        rw [he] at hh
        exact hne hh
      obtain ⟨q,hq⟩ := hr ⟨r.σ d.symm,hs',hfix⟩ true
      exact ⟨q,hq.trans (r.old_corner_label d.symm).symm⟩
  intro z
  induction z using Quotient.inductionOn with
  | _ x =>
    rcases x with ⟨x,b⟩
    by_cases hx : x = d
    · subst x
      cases b
      · exact hdf
      · obtain ⟨q,hq⟩ := hdrf
        exact ⟨q,hq.trans (r.old_cross_label d ht).symm⟩
    · by_cases hxr : x = d.symm
      · subst x
        cases b
        · exact hdrf
        · obtain ⟨q,hq⟩ := hdf
          exact ⟨q,hq.trans hxrev.symm⟩
      · exact hr ⟨x,hx,hxr⟩ b

theorem contract_faces_lower_of_nonfixed (ht : r.twist d = false) (hd : r.σ d ≠ d) :
    Nat.card r.Face ≤ Nat.card (r.contractRotation d hc).Face := by
  classical
  letI : Finite (r.contractRotation d hc).Face :=
    Finite.of_surjective (Quotient.mk _ : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd) → (r.contractRotation d hc).Face)
      (fun q => Quotient.exists_rep q)
  exact Nat.card_le_card_of_surjective _ (r.contractFaceMap_surjective_of_nonfixed d hc ht hd)

theorem contract_genus_le_connected_nonfixed (ht : r.twist d = false)
    (hd : r.σ d ≠ d) (hG : G.Connected) :
    (r.contractRotation d hc).eulerGenus ≤ r.eulerGenus := by
  classical
  let H := SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd
  let q := r.contractRotation d hc
  have hs : r.σ d ≠ d.symm := by
    intro he
    have hh := r.σ_source d
    rw [he] at hh
    exact d.adj.ne hh.symm
  let z : H.Dart := contractionDartMap d ⟨r.σ d,hd,hs⟩
  letI : Nontrivial V := ⟨⟨d.fst,d.snd,d.adj.ne⟩⟩
  letI : Nontrivial (SimpleGraph.EdgeContraction.ContrVertex d.fst d.snd) :=
    ⟨⟨z.fst,z.snd,z.adj.ne⟩⟩
  letI : Nonempty G.Dart := ⟨d⟩
  letI : Nonempty H.Dart := ⟨z⟩
  have hH : H.Connected := SimpleGraph.EdgeContraction.contrGraph_connected G hG
  have hcomp₁ := r.component_card_of_connected hG
  have hcomp₂ := q.component_card_of_connected hH
  have hv₁ := r.vertex_card
  have hv₂ := q.vertex_card
  rw [hG.preconnected.support_eq_univ] at hv₁
  rw [hH.preconnected.support_eq_univ] at hv₂
  simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv] at hv₁ hv₂
  have hv := SimpleGraph.EdgeContraction.contrVertex_card_eq d.adj.ne
  have hvpos : 0 < Fintype.card V := Fintype.card_pos
  have he := contract_edge_card d hc
  have he₁ := r.edge_card
  have he₂ := q.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he₁ he₂
  have hf := r.contract_faces_lower_of_nonfixed d hc ht hd
  change Nat.card r.Face ≤ Nat.card q.Face at hf
  unfold eulerGenus eulerCharacteristic
  change 2 * (Nat.card q.Component : ℤ) - ((Nat.card q.Vertex : ℤ) - (Nat.card q.Edge : ℤ) + (Nat.card q.Face : ℤ)) ≤ _
  rw [hcomp₁,hcomp₂,hv₁,hv₂,he₁,he₂]
  dsimp only [H] at *
  omega

theorem contractFaceMap_surjective_of_reverse_nonfixed (ht : r.twist d = false)
    (hd : r.σ d.symm ≠ d.symm) : Function.Surjective (r.contractFaceMap d hc ht) := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  have hr (x : ContractionDart d) (b : Bool) :
      ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (x.val,b) : r.Face) :=
    ⟨Quotient.mk _ (contractionDartEquiv d hc x,b),r.contractFaceMap_mk d hc ht x b⟩
  have hxrev := r.old_cross_label d.symm (by simpa only [r.twist_symm] using ht)
  have hs : r.σ d.symm ≠ d := by
    intro he
    have hh := r.σ_source d.symm
    rw [he] at hh
    exact hne hh
  have hdrf : ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (d.symm,false) : r.Face) := by
    obtain ⟨q,hq⟩ := hr ⟨r.σ d.symm,hs,hd⟩ true
    exact ⟨q,hq.trans (r.old_corner_label d.symm).symm⟩
  have hdf : ∃ q, r.contractFaceMap d hc ht q = (Quotient.mk _ (d,false) : r.Face) := by
    by_cases hfix : r.σ d = d
    · obtain ⟨q,hq⟩ := hdrf
      have hh := r.old_corner_label d
      rw [hfix] at hh
      exact ⟨q,hq.trans (hh.trans (r.old_cross_label d ht)).symm⟩
    · have hs' : r.σ d ≠ d.symm := by
        intro he
        have hh := r.σ_source d
        rw [he] at hh
        exact hne hh.symm
      obtain ⟨q,hq⟩ := hr ⟨r.σ d,hfix,hs'⟩ true
      exact ⟨q,hq.trans (r.old_corner_label d).symm⟩
  intro z
  induction z using Quotient.inductionOn with
  | _ x =>
    rcases x with ⟨x,b⟩
    by_cases hx : x = d
    · subst x
      cases b
      · exact hdf
      · obtain ⟨q,hq⟩ := hdrf
        exact ⟨q,hq.trans (r.old_cross_label d ht).symm⟩
    · by_cases hxr : x = d.symm
      · subst x
        cases b
        · exact hdrf
        · obtain ⟨q,hq⟩ := hdf
          exact ⟨q,hq.trans hxrev.symm⟩
      · exact hr ⟨x,hx,hxr⟩ b

theorem contract_faces_lower_of_either_nonfixed (ht : r.twist d = false)
    (hd : r.σ d ≠ d ∨ r.σ d.symm ≠ d.symm) :
    Nat.card r.Face ≤ Nat.card (r.contractRotation d hc).Face := by
  classical
  letI : Finite (r.contractRotation d hc).Face :=
    Finite.of_surjective (Quotient.mk _ : Flag (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd) → (r.contractRotation d hc).Face)
      (fun q => Quotient.exists_rep q)
  apply Nat.card_le_card_of_surjective (r.contractFaceMap d hc ht)
  rcases hd with hd | hd
  · exact r.contractFaceMap_surjective_of_nonfixed d hc ht hd
  · exact r.contractFaceMap_surjective_of_reverse_nonfixed d hc ht hd

theorem contract_genus_le_connected_either_nonfixed (ht : r.twist d = false)
    (hd : r.σ d ≠ d ∨ r.σ d.symm ≠ d.symm) (hG : G.Connected) :
    (r.contractRotation d hc).eulerGenus ≤ r.eulerGenus := by
  classical
  let H := SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd
  let q := r.contractRotation d hc
  have hex : Nonempty (ContractionDart d) := by
    rcases hd with hd | hd
    · have hs : r.σ d ≠ d.symm := by
        intro he
        have hh := r.σ_source d
        rw [he] at hh
        exact d.adj.ne hh.symm
      exact ⟨⟨r.σ d,hd,hs⟩⟩
    · have hs : r.σ d.symm ≠ d := by
        intro he
        have hh := r.σ_source d.symm
        rw [he] at hh
        exact d.adj.ne hh
      exact ⟨⟨r.σ d.symm,hs,hd⟩⟩
  let z : H.Dart := contractionDartMap d (Classical.choice hex)
  letI : Nontrivial V := ⟨⟨d.fst,d.snd,d.adj.ne⟩⟩
  letI : Nontrivial (SimpleGraph.EdgeContraction.ContrVertex d.fst d.snd) :=
    ⟨⟨z.fst,z.snd,z.adj.ne⟩⟩
  letI : Nonempty G.Dart := ⟨d⟩
  letI : Nonempty H.Dart := ⟨z⟩
  have hH : H.Connected := SimpleGraph.EdgeContraction.contrGraph_connected G hG
  have hcomp₁ := r.component_card_of_connected hG
  have hcomp₂ := q.component_card_of_connected hH
  have hv₁ := r.vertex_card
  have hv₂ := q.vertex_card
  rw [hG.preconnected.support_eq_univ] at hv₁
  rw [hH.preconnected.support_eq_univ] at hv₂
  simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv] at hv₁ hv₂
  have hv := SimpleGraph.EdgeContraction.contrVertex_card_eq d.adj.ne
  have hvpos : 0 < Fintype.card V := Fintype.card_pos
  have he := contract_edge_card d hc
  have he₁ := r.edge_card
  have he₂ := q.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he₁ he₂
  have hf := r.contract_faces_lower_of_either_nonfixed d hc ht hd
  change Nat.card r.Face ≤ Nat.card q.Face at hf
  unfold eulerGenus eulerCharacteristic
  change 2 * (Nat.card q.Component : ℤ) - ((Nat.card q.Vertex : ℤ) - (Nat.card q.Edge : ℤ) + (Nat.card q.Face : ℤ)) ≤ _
  rw [hcomp₁,hcomp₂,hv₁,hv₂,he₁,he₂]
  dsimp only [H] at *
  omega

theorem dart_eq_of_source_fixed (hfix : r.σ d = d) (x : G.Dart) (hx : x.fst = d.fst) : x = d := by
  obtain ⟨n,hn⟩ := (r.cyclic d x hx.symm).exists_nat_pow_eq
  have hp : ∀ n : ℕ, (r.σ ^ n) d = d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,ih,hfix]
  exact hn.symm.trans (hp n)

theorem connected_vertices_of_both_fixed (hfix : r.σ d = d) (hrev : r.σ d.symm = d.symm)
    (hG : G.Connected) (w : V) : w = d.fst ∨ w = d.snd := by
  have hclosed : ∀ a b, (a = d.fst ∨ a = d.snd) → G.Adj a b → (b = d.fst ∨ b = d.snd) := by
    intro a b ha hab
    rcases ha with ha | ha
    · have he := r.dart_eq_of_source_fixed d hfix (⟨(a,b),hab⟩ : G.Dart) ha
      exact Or.inr (congrArg (fun x : G.Dart => x.snd) he)
    · have he := r.dart_eq_of_source_fixed d.symm hrev (⟨(a,b),hab⟩ : G.Dart) ha
      exact Or.inl (congrArg (fun x : G.Dart => x.snd) he)
  have hwalk : ∀ {a b : V}, G.Walk a b → (a = d.fst ∨ a = d.snd) → (b = d.fst ∨ b = d.snd) := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hclosed a b ha hab)
  obtain ⟨p⟩ := hG.preconnected d.fst w
  exact hwalk p (Or.inl rfl)

theorem contract_genus_le_connected_both_fixed
    (hfix : r.σ d = d) (hrev : r.σ d.symm = d.symm) (hG : G.Connected) :
    (r.contractRotation d hc).eulerGenus ≤ r.eulerGenus := by
  classical
  have he (w : V) : SimpleGraph.EdgeContraction.contrMk d.fst d.snd w =
      SimpleGraph.EdgeContraction.contrMk d.fst d.snd d.fst := by
    rcases r.connected_vertices_of_both_fixed d hfix hrev hG w with h | h
    · rw [h]
    · rw [h]
      exact (SimpleGraph.EdgeContraction.contrMk_eq _ _).symm
  letI : Subsingleton (SimpleGraph.EdgeContraction.ContrVertex d.fst d.snd) := ⟨by
    intro a b
    obtain ⟨x,rfl⟩ := SimpleGraph.EdgeContraction.contrMk_surjective d.fst d.snd a
    obtain ⟨y,rfl⟩ := SimpleGraph.EdgeContraction.contrMk_surjective d.fst d.snd b
    exact (he x).trans (he y).symm⟩
  letI : IsEmpty (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd).Dart :=
    ⟨fun x => x.adj.ne (Subsingleton.elim _ _)⟩
  rw [(r.contractRotation d hc).eulerGenus_eq_zero_of_no_darts]
  exact eulerGenus_nonneg G r

theorem contract_genus_le_connected_untwisted (ht : r.twist d = false) (hG : G.Connected) :
    (r.contractRotation d hc).eulerGenus ≤ r.eulerGenus := by
  by_cases hfix : r.σ d = d
  · by_cases hrev : r.σ d.symm = d.symm
    · exact r.contract_genus_le_connected_both_fixed d hc hfix hrev hG
    · exact r.contract_genus_le_connected_either_nonfixed d hc ht (Or.inr hrev) hG
  · exact r.contract_genus_le_connected_either_nonfixed d hc ht (Or.inl hfix) hG

include hc in
theorem exists_contract_genus_le_connected_no_common (hG : G.Connected) :
    ∃ q : SignedRotation (SimpleGraph.EdgeContraction.contrGraph G d.fst d.snd),
      q.eulerGenus ≤ r.eulerGenus := by
  obtain ⟨s,ht,hg⟩ := r.exists_untwisted_same_genus d
  exact ⟨s.contractRotation d hc, (s.contract_genus_le_connected_untwisted d hc ht hG).trans (le_of_eq hg)⟩

end SimpleGraph.SignedRotation









