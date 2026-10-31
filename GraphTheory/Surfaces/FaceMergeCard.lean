import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic
namespace Paper.FaceSurgery
variable {X : Type*}
def mergeTwo (a b : X) : Setoid X where
  r x y := x = y ∨ (x = a ∨ x = b) ∧ (y = a ∨ y = b)
  iseqv := ⟨fun _ => Or.inl rfl, by aesop, by aesop⟩

theorem mergeTwo_card [Finite X] (a b : X) :
    Nat.card X ≤ Nat.card (Quotient (mergeTwo a b)) + 1 := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Finite (Quotient (mergeTwo a b)) :=
    Finite.of_surjective (Quotient.mk _) (fun q => Quotient.exists_rep q)
  let f : {x : X // x ≠ b} → Quotient (mergeTwo a b) := fun x => Quotient.mk _ x.val
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hr := Quotient.exact h
    change x.val = y.val ∨ (x.val = a ∨ x.val = b) ∧ (y.val = a ∨ y.val = b) at hr
    rcases hr with hr | ⟨hx,hy⟩
    · exact hr
    · rcases hx with hx | hx
      · rcases hy with hy | hy
        · exact hx.trans hy.symm
        · exact (y.property hy).elim
      · exact (x.property hx).elim
  have hc := Nat.card_le_card_of_injective f hf
  have hn : Nat.card {x : X // x ≠ b} + 1 = Nat.card X := by
    simp only [Nat.card_eq_fintype_card]
    have hsum := Fintype.card_subtype_compl (fun x : X => x = b)
    simp only [Fintype.card_unique] at hsum
    change Fintype.card {x : X // x ≠ b} = Fintype.card X - 1 at hsum
    have hp : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨b⟩
    omega
  omega
end Paper.FaceSurgery
