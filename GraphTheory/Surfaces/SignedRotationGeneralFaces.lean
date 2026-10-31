import GraphTheory.Surfaces.SignedRotationFaceFlags
import GraphTheory.Surfaces.SignedRotationNoSquares

/-! The six-flag bound includes leaves in connected graphs of order at least three. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

theorem edgeFlip_ne_cornerFlip (x : Flag G) : r.edgeFlip x ≠ r.cornerFlip x := by
  intro h
  have ht := congrArg (fun z : Flag G => z.1.fst) h
  change x.1.snd = (r.cornerFlip x).1.fst at ht
  rw [r.cornerFlip_source] at ht
  exact x.1.fst_ne_snd ht.symm

theorem sixFlags_injective_of_connected (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) (x : Flag G) : Function.Injective (r.sixFlags x) := by
  have he := r.edgeFlip_involutive
  have hc := r.cornerFlip_involutive
  have hen := r.edgeFlip_ne_self
  have hcn := r.cornerFlip_ne_self
  have hec := r.edgeFlip_ne_cornerFlip
  have hs := r.no_face_square hG hn
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
    simp [sixFlags, baseFlag] at h ⊢
  all_goals grind only [Function.Involutive]

theorem face_flag_bound_of_connected (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) : 6 * Nat.card r.Face ≤ Fintype.card (Flag G) := by
  classical
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Fintype r.Face := Fintype.ofFinite _
  let f : r.Face × (Fin 3 × Bool) → Flag G := fun z => r.sixFlags z.1.out z.2
  have hf : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have hab : a = b := by
      have he := congrArg r.faceOf h
      change r.faceOf (r.sixFlags a.out i) = r.faceOf (r.sixFlags b.out j) at he
      rw [faceOf_sixFlags, faceOf_sixFlags] at he
      simpa only [faceOf, Quotient.out_eq] using he
    subst b
    exact Prod.ext rfl (r.sixFlags_injective_of_connected hG hn a.out h)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm] using hc

theorem face_edge_bound_of_connected (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) : 3 * Nat.card r.Face ≤ 2 * G.edgeFinset.card := by
  have h := r.face_flag_bound_of_connected hG hn
  rw [flag_card] at h
  omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.sixFlags_injective_of_connected
#print axioms SimpleGraph.SignedRotation.face_edge_bound_of_connected
