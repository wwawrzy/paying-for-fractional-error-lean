import GraphTheory.Surfaces.SignedRotationContractionSplice
namespace SimpleGraph.SignedRotation
open Equiv Equiv.Perm
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneChordCountBound
open PlaneTopology.PlaneEdgeGluingPermutation PlaneTopology.PlanePermutationDeletion
open SimpleGraph.EdgeContraction
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] (r : SignedRotation G) (d : G.Dart)
theorem contractionDartMap_injective
    (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w)) :
    Function.Injective (contractionDartMap d) := by
  intro x y hxy
  have hs := congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst) hxy
  have ht := congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.snd) hxy
  change contrMk d.fst d.snd x.val.fst = contrMk d.fst d.snd y.val.fst at hs
  change contrMk d.fst d.snd x.val.snd = contrMk d.fst d.snd y.val.snd at ht
  have hx := contractionDart_distinct d x
  have hadjx := x.val.adj
  have hadjy := y.val.adj
  have hadjxs := hadjx.symm
  have hadjys := hadjy.symm
  apply Subtype.val_injective
  apply Dart.ext
  rcases (contrMk_eq_iff d.fst d.snd x.val.fst y.val.fst).mp hs with hs | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rcases (contrMk_eq_iff d.fst d.snd x.val.snd y.val.snd).mp ht with ht | ⟨he,hf⟩ | ⟨he,hf⟩
  · exact Prod.ext hs ht
  all_goals first
    | solve | simp_all only [contrMk_eq, not_true_eq_false]
    | solve | exfalso; apply hc x.val.snd; aesop
    | solve | exfalso; apply hc x.val.fst; aesop

noncomputable def contractionDartEquiv
    (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w)) :
    ContractionDart d ≃ (contrGraph G d.fst d.snd).Dart :=
  Equiv.ofBijective (contractionDartMap d)
    ⟨contractionDartMap_injective d hc, contractionDartMap_surjective d⟩

def contractionDartReverse (x : ContractionDart d) : ContractionDart d :=
  ⟨x.val.symm, by
    constructor
    · intro h
      apply x.property.2
      simpa using congrArg Dart.symm h
    · intro h
      apply x.property.1
      simpa using congrArg Dart.symm h⟩

theorem contractionDartMap_reverse (x : ContractionDart d) :
    contractionDartMap d (contractionDartReverse d x) = (contractionDartMap d x).symm := rfl

noncomputable def contractRotation
    (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w)) :
    SignedRotation (contrGraph G d.fst d.snd) where
  σ := (contractionDartEquiv d hc).permCongr (r.contractionDartPerm d)
  σ_source x := by
    let e := contractionDartEquiv d hc
    have he (a : ContractionDart d) : (e a).fst = contrMk d.fst d.snd a.val.fst := rfl
    change (e (r.contractionDartPerm d (e.symm x))).fst = x.fst
    rw [he, r.contractionDartPerm_source d]
    exact (he (e.symm x)).symm.trans (congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst) (e.apply_symm_apply x))
  cyclic x y h := by
    let e := contractionDartEquiv d hc
    have hx : contrMk d.fst d.snd (e.symm x).val.fst = x.fst :=
      congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst) (e.apply_symm_apply x)
    have hy : contrMk d.fst d.snd (e.symm y).val.fst = y.fst :=
      congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst) (e.apply_symm_apply y)
    have hh := r.contractionDartPerm_cyclic d (e.symm x) (e.symm y) (hx.trans (h.trans hy.symm))
    have hm := sameCycle_map (r.contractionDartPerm d) (e.permCongr (r.contractionDartPerm d))
      e (fun a => by simp) hh
    simpa only [Equiv.apply_symm_apply] using hm
  twist x := r.twist ((contractionDartEquiv d hc).symm x).val
  twist_symm x := by
    let e := contractionDartEquiv d hc
    have he : e.symm x.symm = contractionDartReverse d (e.symm x) := by
      apply e.injective
      change e (e.symm x.symm) = contractionDartMap d (contractionDartReverse d (e.symm x))
      rw [e.apply_symm_apply, contractionDartMap_reverse]
      change x.symm = (e (e.symm x)).symm
      rw [e.apply_symm_apply]
    change r.twist (e.symm x.symm).val = r.twist (e.symm x).val
    rw [he]
    exact r.twist_symm _

theorem contractionDart_card : Nat.card (ContractionDart d) + 2 = Nat.card G.Dart := by
  classical
  have hne : d ≠ d.symm := by
    intro h
    have he := congrArg (fun x : G.Dart => x.fst) h
    change d.fst = d.snd at he
    exact G.irrefl (he ▸ d.adj)
  have hc : Fintype.card {x : G.Dart // x = d ∨ x = d.symm} = 2 := by
    rw [Fintype.card_subtype]
    have he : Finset.univ.filter (fun x : G.Dart => x = d ∨ x = d.symm) = {d,d.symm} := by
      ext x
      simp
    rw [he,Finset.card_pair hne]
  have htotal : 2 ≤ Fintype.card G.Dart := by
    rw [← hc]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hm := Fintype.card_subtype_compl (fun x : G.Dart => x = d ∨ x = d.symm)
  have he : {x : G.Dart // ¬ (x = d ∨ x = d.symm)} ≃ ContractionDart d :=
    Equiv.subtypeEquivRight (fun _ => not_or)
  rw [Fintype.card_congr he,hc] at hm
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  omega

theorem contract_edge_card
    (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w)) :
    Nat.card (contrGraph G d.fst d.snd).edgeSet + 1 = Nat.card G.edgeSet := by
  classical
  have hh := contractionDart_card d
  have he := Nat.card_congr (contractionDartEquiv d hc)
  rw [he] at hh
  simp only [Nat.card_eq_fintype_card,SimpleGraph.dart_card_eq_twice_card_edges,
    ← SimpleGraph.edgeFinset_card] at hh ⊢
  omega

end SimpleGraph.SignedRotation
