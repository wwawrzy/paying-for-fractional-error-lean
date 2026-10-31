import GraphTheory.Surfaces.SignedRotation
import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.Plane.PlaneEdgeGluingPermutation
import GraphTheory.Plane.PlanePermutationDeletion
namespace SimpleGraph.SignedRotation
open Equiv Equiv.Perm
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneChordCountBound
open PlaneTopology.PlaneEdgeGluingPermutation
open SimpleGraph.EdgeContraction
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] (r : SignedRotation G) (d : G.Dart)
noncomputable def contractionSplice : Perm G.Dart := swap d d.symm * r.σ

theorem contractionSplice_source (x : G.Dart) :
    contrMk d.fst d.snd (r.contractionSplice d x).fst = contrMk d.fst d.snd x.fst := by
  change (fun z : G.Dart => contrMk d.fst d.snd z.fst) (swap d d.symm (r.σ x)) = _
  have he : (fun z : G.Dart => contrMk d.fst d.snd z.fst) d =
      (fun z : G.Dart => contrMk d.fst d.snd z.fst) d.symm := contrMk_eq _ _
  exact (map_swap_eq (fun z : G.Dart => contrMk d.fst d.snd z.fst) d d.symm (r.σ x) he).trans
    (congrArg (contrMk d.fst d.snd) (r.σ_source x))

theorem endpoints_not_sameCycle : ¬ r.σ.SameCycle d d.symm := by
  intro h
  have he := sameCycle_label r.σ (fun x : G.Dart => x.fst) r.σ_source h
  change d.fst = d.snd at he
  exact G.irrefl (he ▸ d.adj)

theorem contractionSplice_cyclic (x y : G.Dart)
    (h : contrMk d.fst d.snd x.fst = contrMk d.fst d.snd y.fst) :
    (r.contractionSplice d).SameCycle x y := by
  have hp {a b : G.Dart} (hab : a.fst = b.fst) :
      (r.contractionSplice d).SameCycle a b :=
    sameCycle_swap_mul_preserved r.σ d d.symm (r.endpoints_not_sameCycle d) (r.cyclic a b hab)
  have hj : (r.contractionSplice d).SameCycle d d.symm :=
    sameCycle_swap_mul_of_not_sameCycle r.σ d d.symm (r.endpoints_not_sameCycle d)
  rcases (contrMk_eq_iff d.fst d.snd x.fst y.fst).mp h with he | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact hp he
  · exact (hp hx).trans (hj.trans (hp hy.symm))
  · exact (hp hx).trans (hj.symm.trans (hp hy.symm))
open PlaneTopology.PlanePermutationDeletion
/-- Bypass both contracted darts in the merged vertex cycle. -/
noncomputable def contractionErased : Perm G.Dart :=
  erasePoint (erasePoint (r.contractionSplice d) d.symm) d

theorem contractionErased_fixed : r.contractionErased d d = d ∧
    r.contractionErased d d.symm = d.symm := by
  have hne : d.symm ≠ d := by
    intro h
    have he := congrArg (fun x : G.Dart => x.fst) h
    change d.snd = d.fst at he
    exact G.irrefl (he ▸ d.adj)
  constructor
  · exact erasePoint_fixed _ _
  · rw [contractionErased, erasePoint_apply_of_ne _ _ _ hne]
    · exact erasePoint_fixed _ _
    · rw [erasePoint_fixed]
      exact hne

theorem contractionErased_source (x : G.Dart) :
    contrMk d.fst d.snd (r.contractionErased d x).fst = contrMk d.fst d.snd x.fst := by
  exact erasePoint_preserves _ _ (fun z : G.Dart => contrMk d.fst d.snd z.fst)
    (fun z => erasePoint_preserves (r.contractionSplice d) d.symm
      (fun z : G.Dart => contrMk d.fst d.snd z.fst) (r.contractionSplice_source d) z) x

theorem contractionErased_cyclic (x y : G.Dart)
    (hx : x ≠ d) (hxr : x ≠ d.symm) (hy : y ≠ d) (hyr : y ≠ d.symm)
    (h : contrMk d.fst d.snd x.fst = contrMk d.fst d.snd y.fst) :
    (r.contractionErased d).SameCycle x y := by
  apply erasePoint_sameCycle _ _ hx hy
  apply erasePoint_sameCycle _ _ hxr hyr
  exact r.contractionSplice_cyclic d x y h

/-- Actual dart carrier before simplifying parallel edges. -/
abbrev ContractionDart := {x : G.Dart // x ≠ d ∧ x ≠ d.symm}

theorem contractionErased_survives (x : G.Dart) :
    (r.contractionErased d x ≠ d ∧ r.contractionErased d x ≠ d.symm) ↔
      (x ≠ d ∧ x ≠ d.symm) := by
  have hf := r.contractionErased_fixed d
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun h => h₁ (h ▸ hf.1), fun h => h₂ (h ▸ hf.2)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun h => h₁ ((r.contractionErased d).injective (h.trans hf.1.symm)),
      fun h => h₂ ((r.contractionErased d).injective (h.trans hf.2.symm))⟩

noncomputable def contractionDartPerm : Perm (ContractionDart d) :=
  (r.contractionErased d).subtypePerm (r.contractionErased_survives d)

theorem contractionDartPerm_source (x : ContractionDart d) :
    contrMk d.fst d.snd (r.contractionDartPerm d x).val.fst =
      contrMk d.fst d.snd x.val.fst := r.contractionErased_source d x.val

theorem contractionDartPerm_cyclic (x y : ContractionDart d)
    (h : contrMk d.fst d.snd x.val.fst = contrMk d.fst d.snd y.val.fst) :
    (r.contractionDartPerm d).SameCycle x y := by
  apply sameCycle_reflect (r.contractionDartPerm d) (r.contractionErased d)
    Subtype.val Subtype.val_injective (fun _ => rfl)
  exact r.contractionErased_cyclic d x.val y.val x.property.1 x.property.2
    y.property.1 y.property.2 h

theorem contractionDart_distinct (x : ContractionDart d) :
    contrMk d.fst d.snd x.val.fst ≠ contrMk d.fst d.snd x.val.snd := by
  intro h
  rcases (contrMk_eq_iff d.fst d.snd x.val.fst x.val.snd).mp h with he | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact G.irrefl (he ▸ x.val.adj)
  · apply x.property.1
    apply Dart.ext
    exact Prod.ext ha hb
  · apply x.property.2
    apply Dart.ext
    exact Prod.ext ha hb

noncomputable def contractionDartMap (x : ContractionDart d) :
    (contrGraph G d.fst d.snd).Dart :=
  ⟨(contrMk d.fst d.snd x.val.fst, contrMk d.fst d.snd x.val.snd),
    contrGraph_adj_of_adj G d.fst d.snd x.val.adj (contractionDart_distinct d x)⟩

theorem contractionDartMap_surjective : Function.Surjective (contractionDartMap d) := by
  intro z
  obtain ⟨a,b,ha,hb,hab⟩ := z.adj.2
  let x : G.Dart := ⟨(a,b),hab⟩
  have hne : contrMk d.fst d.snd a ≠ contrMk d.fst d.snd b := by
    rw [ha,hb]
    exact z.adj.1
  have hx : x ≠ d ∧ x ≠ d.symm := by
    constructor
    · intro he
      apply hne
      change contrMk d.fst d.snd x.fst = contrMk d.fst d.snd x.snd
      rw [he]
      exact contrMk_eq _ _
    · intro he
      apply hne
      change contrMk d.fst d.snd x.fst = contrMk d.fst d.snd x.snd
      rw [he]
      exact (contrMk_eq _ _).symm
  refine ⟨⟨x,hx⟩, ?_⟩
  apply Dart.ext
  exact Prod.ext ha hb

end SimpleGraph.SignedRotation





