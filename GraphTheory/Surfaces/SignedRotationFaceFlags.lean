import GraphTheory.Surfaces.SignedRotationCorners

/-! Six distinct flags per face in a simple graph of minimum degree two. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)

def baseFlag (x : Flag G) (i : Fin 3) : Flag G :=
  if i = 0 then x else if i = 1 then r.cornerFlip x else r.cornerFlip (r.edgeFlip x)

def sixFlags (x : Flag G) (i : Fin 3 × Bool) : Flag G :=
  if i.2 then r.edgeFlip (r.baseFlag x i.1) else r.baseFlag x i.1

def faceOf (x : Flag G) : r.Face := Quotient.mk _ x

@[simp] theorem edgeFlip_edge (x : Flag G) : (r.edgeFlip x).1.edge = x.1.edge :=
  x.1.edge_symm

@[simp] theorem faceOf_edgeFlip (x : Flag G) : r.faceOf (r.edgeFlip x) = r.faceOf x := by
  apply Eq.symm
  exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl rfl))

@[simp] theorem faceOf_cornerFlip (x : Flag G) : r.faceOf (r.cornerFlip x) = r.faceOf x := by
  apply Eq.symm
  exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr rfl))

@[simp] theorem faceOf_sixFlags (x : Flag G) (i : Fin 3 × Bool) :
    r.faceOf (r.sixFlags x i) = r.faceOf x := by
  rcases i with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [sixFlags, baseFlag]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (hdeg : ∀ v, 2 ≤ G.degree v)

include hdeg

theorem baseFlag_edges_injective (x : Flag G) :
    Function.Injective (fun i => (r.baseFlag x i).1.edge) := by
  have h₁ := r.cornerFlip_edge_ne hdeg x
  have h₂ : (r.cornerFlip (r.edgeFlip x)).1.edge ≠ x.1.edge := by
    simpa using r.cornerFlip_edge_ne hdeg (r.edgeFlip x)
  have h₃ := r.endpoint_corner_edges_ne hdeg x
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [baseFlag]

theorem sixFlags_injective (x : Flag G) : Function.Injective (r.sixFlags x) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have he := congrArg (fun z : Flag G => z.1.edge) h
  have hi : i = j := r.baseFlag_edges_injective hdeg x (by
    cases b <;> cases c <;> simpa [sixFlags] using he)
  subst j
  have hn := r.edgeFlip_ne_self (r.baseFlag x i)
  cases b <;> cases c
  · rfl
  · change r.baseFlag x i = r.edgeFlip (r.baseFlag x i) at h
    exact (hn h.symm).elim
  · change r.edgeFlip (r.baseFlag x i) = r.baseFlag x i at h
    exact (hn h).elim
  · rfl

theorem face_flag_bound : 6 * Nat.card r.Face ≤ Fintype.card (Flag G) := by
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
    exact Prod.ext rfl (r.sixFlags_injective hdeg a.out h)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm] using hc

theorem face_edge_bound : 3 * Nat.card r.Face ≤ 2 * G.edgeFinset.card := by
  have h := r.face_flag_bound hdeg
  rw [flag_card] at h
  omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.sixFlags_injective
#print axioms SimpleGraph.SignedRotation.face_flag_bound
#print axioms SimpleGraph.SignedRotation.face_edge_bound
