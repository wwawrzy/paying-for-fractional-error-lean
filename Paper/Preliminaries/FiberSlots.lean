import Mathlib

/-! Assign distinct local slots whenever every physical fiber has bounded
cardinality. This separates candidate and set roles in a clique blowup. -/
namespace Paper.FiberSlots
attribute [local instance] Classical.propDecidable
variable {A V : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]

theorem exists_slots (p : A → V) (m : ℕ)
    (h : ∀ v, Fintype.card {a // p a = v} ≤ m) :
    ∃ slot : A → Fin m, Function.Injective (fun a => (p a, slot a)) := by
  classical
  let g : (Σ v, {a // p a = v}) → V × Fin m := fun z =>
    (z.1, Fin.castLE (h z.1) ((Fintype.equivFin {a // p a = z.1}) z.2))
  have hg : Function.Injective g := by
    rintro ⟨v, a⟩ ⟨w, b⟩ he
    have hw : v = w := congrArg (fun x : V × Fin m => x.1) he
    subst w
    have hs := congrArg (fun x : V × Fin m => x.2.val) he
    have hi : (Fintype.equivFin {a // p a = v}) a = (Fintype.equivFin {a // p a = v}) b := Fin.ext hs
    have hab := (Fintype.equivFin {a // p a = v}).injective hi
    subst b
    rfl
  let embed := fun a : A => g ⟨p a, ⟨a, rfl⟩⟩
  refine ⟨fun a => (embed a).2, ?_⟩
  intro a b he
  have he' : embed a = embed b := he
  have hh := hg he'
  exact congrArg (fun z : Σ v, {a // p a = v} => z.2.val) hh
end Paper.FiberSlots
