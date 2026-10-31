import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.Surfaces.SignedRotationComponents
import GraphTheory.Surfaces.SignedRotationContractionFaces
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V) (huv : G.Adj u v)
def contractionComponentLabel : ContrVertex u v → G.ConnectedComponent :=
  Quotient.lift G.connectedComponentMk (by
    intro a b h
    rcases (eqvGen_pairRel_iff u v a b).mp h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [h]
    · exact ConnectedComponent.sound huv.reachable
    · exact ConnectedComponent.sound huv.symm.reachable)

theorem contractionComponentLabel_adj {x y : ContrVertex u v}
    (h : (contrGraph G u v).Adj x y) :
    contractionComponentLabel G u v huv x = contractionComponentLabel G u v huv y := by
  obtain ⟨_,a,b,ha,hb,hab⟩ := h
  rw [← ha,← hb]
  exact ConnectedComponent.sound hab.reachable

theorem contractionComponentLabel_walk {x y : ContrVertex u v}
    (p : (contrGraph G u v).Walk x y) :
    contractionComponentLabel G u v huv x = contractionComponentLabel G u v huv y := by
  induction p with
  | nil => rfl
  | cons hab p ih => exact (contractionComponentLabel_adj G u v huv hab).trans ih

include huv in
theorem contraction_reachable_iff (a b : V) :
    (contrGraph G u v).Reachable (contrMk u v a) (contrMk u v b) ↔ G.Reachable a b := by
  constructor
  · rintro ⟨p⟩
    exact ConnectedComponent.exact (contractionComponentLabel_walk G u v huv p)
  · rintro ⟨p⟩
    exact contrGraph_reachable_of_walk G u v p
noncomputable def contractionComponentForward : G.ConnectedComponent → (contrGraph G u v).ConnectedComponent :=
  ConnectedComponent.lift (fun x => (contrGraph G u v).connectedComponentMk (contrMk u v x))
    (fun _ _ p _ => ConnectedComponent.sound (contrGraph_reachable_of_walk G u v p))

noncomputable def contractionComponentBackward : (contrGraph G u v).ConnectedComponent → G.ConnectedComponent :=
  ConnectedComponent.lift (contractionComponentLabel G u v huv)
    (fun _ _ p _ => contractionComponentLabel_walk G u v huv p)

noncomputable def contractionComponentEquiv : G.ConnectedComponent ≃ (contrGraph G u v).ConnectedComponent where
  toFun := contractionComponentForward G u v
  invFun := contractionComponentBackward G u v huv
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h x => rfl
  right_inv c := by
    induction c using ConnectedComponent.ind with
    | h x => exact Quotient.inductionOn x (fun _ => rfl)

section Flags
variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (r : SignedRotation G) (d : G.Dart)
variable (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w))
theorem contract_component_relation_iff
    (x y : Flag (contrGraph G d.fst d.snd)) :
    (r.contractRotation d hc).ComponentRel x y ↔
      r.ComponentRel (contractPullFlag d hc x) (contractPullFlag d hc y) := by
  classical
  rw [(r.contractRotation d hc).component_relation_iff,r.component_relation_iff]
  have hx : contrMk d.fst d.snd (contractPullFlag d hc x).1.fst = x.1.fst :=
    congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst)
      ((contractionDartEquiv d hc).apply_symm_apply x.1)
  have hy : contrMk d.fst d.snd (contractPullFlag d hc y).1.fst = y.1.fst :=
    congrArg (fun z : (contrGraph G d.fst d.snd).Dart => z.fst)
      ((contractionDartEquiv d hc).apply_symm_apply y.1)
  rw [← hx,← hy]
  exact contraction_reachable_iff G d.fst d.snd d.adj _ _

noncomputable def contractComponentMap : (r.contractRotation d hc).Component → r.Component :=
  Quotient.lift (fun x => Quotient.mk _ (contractPullFlag d hc x))
    (fun x y h => Quotient.sound ((r.contract_component_relation_iff d hc x y).mp h))

theorem contractComponentMap_injective : Function.Injective (r.contractComponentMap d hc) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  apply Quotient.sound
  exact (r.contract_component_relation_iff d hc a b).mpr (Quotient.exact h)

theorem contract_component_card_le : Nat.card (r.contractRotation d hc).Component ≤ Nat.card r.Component := by
  classical
  letI : Finite r.Component := Finite.of_surjective (Quotient.mk _ : Flag G → r.Component)
    (fun q => Quotient.exists_rep q)
  exact Nat.card_le_card_of_injective _ (r.contractComponentMap_injective d hc)
end Flags

end SimpleGraph.SignedRotation


