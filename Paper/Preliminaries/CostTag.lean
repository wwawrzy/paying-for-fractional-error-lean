import Paper.Preliminaries.TaggedMinimum
import Mathlib.Data.Prod.Lex

/-! Graph-independent bounded-cost/ID tag codes and the exact minimum-cost
property of a returned tag. IDs resolve equal-cost ties. -/
namespace Paper.CostTag
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Tag (V : Type) (B : ℕ) := Fin (B + 1) ×ₗ V

def code {b : ℕ} (C : BitCode V b) (B : ℕ) : BitCode (Tag V B) (B + 1 + b) :=
  PacketCode.transport (PacketCode.product (SmallNumberCode.code (B + 1)) C) {
    toFun := toLex
    invFun := ofLex
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def tag {B : ℕ} (cost : V → Fin (B + 1)) (v : V) : Tag V B := toLex (cost v, v)

theorem injective {B : ℕ} (cost : V → Fin (B + 1)) : Function.Injective (tag cost) := by
  intro v w h
  exact congrArg (fun t : Tag V B => (ofLex t).2) h

variable [Fintype V]

theorem least_cost {B : ℕ} (cost : V → Fin (B + 1)) (S : Finset V) {t : Tag V B}
    (h : MaskedMinimum.minimum (S.image (tag cost)) = some t) :
    (ofLex t).2 ∈ S ∧ (ofLex t).1 = cost (ofLex t).2 ∧
      ∀ v ∈ S, (cost (ofLex t).2).val ≤ (cost v).val := by
  obtain ⟨⟨w, hw, he⟩, hleast⟩ := TaggedMinimum.least S (tag cost) h
  subst t
  refine ⟨hw, rfl, ?_⟩
  intro v hv
  exact Prod.Lex.monotone_fst _ _ (hleast v hv)
end Paper.CostTag
