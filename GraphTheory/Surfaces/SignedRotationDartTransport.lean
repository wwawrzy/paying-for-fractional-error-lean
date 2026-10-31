import GraphTheory.Surfaces.SignedRotationSwitch
import GraphTheory.Plane.PlanePermutationSurgery
namespace SimpleGraph.SignedRotation
variable {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
variable [Finite G.Dart]
variable (r : SignedRotation G) (e : G.Dart ≃ H.Dart)
variable (hs : ∀ a b, (e a).fst = (e b).fst ↔ a.fst = b.fst)
variable (hr : ∀ a, e a.symm = (e a).symm)
noncomputable def dartTransport : SignedRotation H where
  σ := e.permCongr r.σ
  σ_source x := by
    change (e (r.σ (e.symm x))).fst = x.fst
    exact ((hs _ _).mpr (r.σ_source _)).trans (congrArg (fun x : H.Dart => x.fst) (e.apply_symm_apply x))
  cyclic x y h := by
    have hh : (e.symm x).fst = (e.symm y).fst := (hs _ _).mp (by simpa using h)
    have hc := r.cyclic (e.symm x) (e.symm y) hh
    classical
    have hm := PlaneTopology.PlanePermutationSurgery.sameCycle_map r.σ (e.permCongr r.σ)
      e (fun a => by simp) hc
    simpa only [Equiv.apply_symm_apply] using hm
  twist x := r.twist (e.symm x)
  twist_symm x := by
    have he : e.symm x.symm = (e.symm x).symm := by
      apply e.injective
      rw [e.apply_symm_apply,hr,e.apply_symm_apply]
    change r.twist (e.symm x.symm) = r.twist (e.symm x)
    rw [he,r.twist_symm]

def dartFlagEquiv : Flag G ≃ Flag H := Equiv.prodCongr e (Equiv.refl Bool)

theorem dartFlagEquiv_side (x : Flag G) :
    dartFlagEquiv e (sideFlip x) = sideFlip (dartFlagEquiv e x) := rfl

theorem dartFlagEquiv_edge (x : Flag G) :
    dartFlagEquiv e (r.edgeFlip x) = (r.dartTransport e hs hr).edgeFlip (dartFlagEquiv e x) := by
  rcases x with ⟨x,b⟩
  change (e x.symm,if r.twist x then b else !b) =
    ((e x).symm,if r.twist (e.symm (e x)) then b else !b)
  rw [hr,e.symm_apply_apply]

theorem dartFlagEquiv_corner (x : Flag G) :
    dartFlagEquiv e (r.cornerFlip x) = (r.dartTransport e hs hr).cornerFlip (dartFlagEquiv e x) := by
  rcases x with ⟨x,b⟩
  cases b
  · simp [dartFlagEquiv,cornerFlip,dartTransport]
  · change (e (r.σ.symm x),false) = (e (r.σ.symm (e.symm (e x))),false)
    rw [e.symm_apply_apply]

noncomputable def dartTransportVertexEquiv : r.Vertex ≃ (r.dartTransport e hs hr).Vertex :=
  Quotient.congr (dartFlagEquiv e) (by
    intro x y
    apply eqvGen_equiv_switch (dartFlagEquiv e)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← dartFlagEquiv_side e, ← r.dartFlagEquiv_corner e hs hr]
    simp only [Equiv.apply_eq_iff_eq])

noncomputable def dartTransportEdgeEquiv : r.Edge ≃ (r.dartTransport e hs hr).Edge :=
  Quotient.congr (dartFlagEquiv e) (by
    intro x y
    apply eqvGen_equiv_switch (dartFlagEquiv e)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← r.dartFlagEquiv_edge e hs hr, ← dartFlagEquiv_side e]
    simp only [Equiv.apply_eq_iff_eq])

noncomputable def dartTransportFaceEquiv : r.Face ≃ (r.dartTransport e hs hr).Face :=
  Quotient.congr (dartFlagEquiv e) (by
    intro x y
    apply eqvGen_equiv_switch (dartFlagEquiv e)
    intro a b
    change (_ ∨ _) ↔ (_ ∨ _)
    rw [← r.dartFlagEquiv_edge e hs hr, ← r.dartFlagEquiv_corner e hs hr]
    simp only [Equiv.apply_eq_iff_eq])

noncomputable def dartTransportComponentEquiv : r.Component ≃ (r.dartTransport e hs hr).Component :=
  Quotient.congr (dartFlagEquiv e) (by
    intro x y
    apply eqvGen_equiv_switch (dartFlagEquiv e)
    intro a b
    change (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
    rw [← r.dartFlagEquiv_edge e hs hr, ← dartFlagEquiv_side e, ← r.dartFlagEquiv_corner e hs hr]
    simp only [Equiv.apply_eq_iff_eq])

theorem dartTransport_eulerGenus : (r.dartTransport e hs hr).eulerGenus = r.eulerGenus := by
  unfold eulerGenus eulerCharacteristic
  rw [← Nat.card_congr (r.dartTransportVertexEquiv e hs hr),
    ← Nat.card_congr (r.dartTransportEdgeEquiv e hs hr),
    ← Nat.card_congr (r.dartTransportFaceEquiv e hs hr),
    ← Nat.card_congr (r.dartTransportComponentEquiv e hs hr)]

end SimpleGraph.SignedRotation

