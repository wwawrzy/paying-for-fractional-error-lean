import Paper.Preliminaries.PacketCode
import Mathlib.Data.Finset.Lattice.Fold

/-! Minimum-ID data as a computable commutative-monoid payload with a
public b+1-bit code. Its zero means no selected identifier. -/
namespace Paper.MinimumPayload
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Data (V : Type) where
  value : WithTop V

instance payloadZero : Zero (Data V) := ⟨⟨⊤⟩⟩

instance payloadAdd : Add (Data V) := ⟨fun a b => ⟨a.value ⊓ b.value⟩⟩

@[ext] theorem ext {a b : Data V} (h : a.value = b.value) : a = b := by
  cases a; cases b
  congr

instance payloadAddCommMonoid : AddCommMonoid (Data V) where
  zero := ⟨⊤⟩
  add a b := ⟨a.value ⊓ b.value⟩
  add_assoc a b c := ext (inf_assoc _ _ _)
  zero_add a := ext (top_inf_eq _)
  add_zero a := ext (inf_top_eq _)
  add_comm a b := ext (inf_comm _ _)
  nsmul := nsmulRec

def code {b : ℕ} (C : BitCode V b) : BitCode (Data V) (b + 1) :=
  PacketCode.transport C.option {
    toFun := fun x => ⟨x⟩
    invFun := Data.value
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def singleton (v : V) : Data V := ⟨(v : WithTop V)⟩

theorem sum_value (S : Finset V) : (∑ v ∈ S, singleton v).value =
    S.inf (fun v => (v : WithTop V)) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert v S hv ih =>
    simp only [Finset.sum_insert hv, Finset.inf_insert]
    change (v : WithTop V) ⊓ (∑ u ∈ S, singleton u).value = _
    rw [ih]

theorem sum_minimum (S : Finset V) (hne : S.Nonempty) :
    (∑ v ∈ S, singleton v).value = ((S.min' hne : V) : WithTop V) := by
  rw [sum_value, Finset.min'_eq_inf', Finset.coe_inf']
  rfl
end Paper.MinimumPayload
