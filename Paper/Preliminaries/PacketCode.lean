import Paper.Communication.BroadcastModel
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual encoders and decoders for fixed products and vectors of messages.
These definitions are graph-independent and computational. -/
namespace Paper.PacketCode
open BroadcastModel

def ofInverse {A : Type*} {b : ℕ} (enc : A → Fin b → Bool) (dec : (Fin b → Bool) → Option A)
    (h : ∀ a, dec (enc a) = some a) : BitCode A b where
  encode := enc
  decode := dec
  leftInverse := h
  injective := by
    intro a a' he
    have hh := congrArg dec he
    rw [h a, h a'] at hh
    exact Option.some.inj hh

def product {A B : Type*} {b c : ℕ} (C : BitCode A b) (D : BitCode B c) : BitCode (A × B) (b + c) :=
  ofInverse
    (fun x => Fin.append (C.encode x.1) (D.encode x.2))
    (fun bits => match C.decode (fun i => bits (i.castAdd c)), D.decode (fun j => bits (j.natAdd b)) with
      | some a, some d => some (a, d)
      | _, _ => none)
    (by
      intro x
      simp only [Fin.append_left, Fin.append_right, C.leftInverse, D.leftInverse])

def sequence {A : Type*} {m : ℕ} (f : Fin m → Option A) : Option (Fin m → A) :=
  if h : ∀ i, (f i).isSome then some (fun i => (f i).get (h i)) else none

theorem sequence_some {A : Type*} {m : ℕ} (f : Fin m → A) : sequence (fun i => some (f i)) = some f := by
  simp [sequence]

def vector {A : Type*} {b : ℕ} (C : BitCode A b) (m : ℕ) : BitCode (Fin m → A) (m * b) :=
  ofInverse
    (fun f j => C.encode (f (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)
    (fun bits => sequence (fun i => C.decode (fun j => bits (finProdFinEquiv (i, j)))))
    (by
      intro f
      have he : (fun i : Fin m => C.decode (fun j =>
          C.encode (f (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
            (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2)) = fun i => some (f i) := by
        funext i
        simp only [Equiv.symm_apply_apply, C.leftInverse]
      dsimp only
      rw [he, sequence_some])

def transport {A B : Type*} {b : ℕ} (C : BitCode A b) (e : A ≃ B) : BitCode B b :=
  ofInverse (fun x => C.encode (e.symm x)) (fun bits => (C.decode bits).map e)
    (fun x => by simp only [C.leftInverse, Option.map_some, Equiv.apply_symm_apply])
end Paper.PacketCode
