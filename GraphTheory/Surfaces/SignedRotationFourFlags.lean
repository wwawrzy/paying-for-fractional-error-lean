import GraphTheory.Surfaces.SignedRotationGeneralFaces

/-! Every face of a signed rotation of a simple graph contains four distinct flags. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

def fourFlags (x : Flag G) (i : Bool × Bool) : Flag G :=
  let y := if i.1 then r.cornerFlip x else x
  if i.2 then r.edgeFlip y else y

theorem fourFlags_injective (x : Flag G) : Function.Injective (r.fourFlags x) := by
  have he := r.edgeFlip_involutive
  have hc := r.cornerFlip_involutive
  have hen := r.edgeFlip_ne_self
  have hcn := r.cornerFlip_ne_self
  have hec := r.edgeFlip_ne_cornerFlip
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  cases a <;> cases b <;> cases c <;> cases d <;> simp [fourFlags] at h ⊢
  all_goals grind only [Function.Involutive]

theorem faceOf_fourFlags (x : Flag G) (i : Bool × Bool) :
    r.faceOf (r.fourFlags x i) = r.faceOf x := by
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;> simp [fourFlags]

theorem four_face_flag_bound : 4 * Nat.card r.Face ≤ Fintype.card (Flag G) := by
  classical
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Fintype r.Face := Fintype.ofFinite _
  let f : r.Face × (Bool × Bool) → Flag G := fun z => r.fourFlags z.1.out z.2
  have hf : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have hab : a = b := by
      have he := congrArg r.faceOf h
      change r.faceOf (r.fourFlags a.out i) = r.faceOf (r.fourFlags b.out j) at he
      rw [faceOf_fourFlags, faceOf_fourFlags] at he
      simpa only [faceOf, Quotient.out_eq] using he
    subst b
    exact Prod.ext rfl (r.fourFlags_injective a.out h)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm] using hc

theorem face_card_le_edge_card : Nat.card r.Face ≤ G.edgeFinset.card := by
  have h := r.four_face_flag_bound
  rw [flag_card] at h
  omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.fourFlags_injective
#print axioms SimpleGraph.SignedRotation.face_card_le_edge_card
