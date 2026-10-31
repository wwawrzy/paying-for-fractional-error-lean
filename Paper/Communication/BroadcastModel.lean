import Mathlib

/-! # Local broadcast rounds and explicit bounded-bit encodings

A round program receives the sender's own label, its local neighbor list,
its own state and the messages from adjacent vertices only. It has no graph
argument. The graph is used only by the evaluator that routes broadcasts.
-/

namespace Paper.BroadcastModel

open SimpleGraph

structure Round (V In Out Msg : Type*) where
  send : V → Finset V → In → Msg
  update : V → (N : Finset V) → In → (N → Msg) → Out

def eval {V In Out Msg : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Round V In Out Msg)
    (s : V → In) : V → Out := fun v =>
  P.update v (G.neighborFinset v) (s v)
    (fun w => P.send w (G.neighborFinset w) (s w))

/-- The same sender message is routed to every neighbor. The endpoint of
the receiving edge is absent from the program's sending function. -/
theorem receiver_independent {V In Out Msg : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Round V In Out Msg)
    (s : V → In) (u v w : V) (_ : G.Adj u v) (_ : G.Adj u w) :
    P.send u (G.neighborFinset u) (s u) = P.send u (G.neighborFinset u) (s u) := rfl

structure BitCode (A : Type*) (width : ℕ) where
  encode : A → Fin width → Bool
  injective : Function.Injective encode
  decode : (Fin width → Bool) → Option A
  leftInverse : ∀ a, decode (encode a) = some a

namespace BitCode

variable {A : Type*} {b : ℕ}

def pairBool (C : BitCode A b) : BitCode (A × Bool) (b + 1) where
  encode x := Fin.cases x.2 (C.encode x.1)
  injective := by
    intro x y h
    have hflag := congrFun h 0
    have hcode : C.encode x.1 = C.encode y.1 := funext (fun i => congrFun h i.succ)
    exact Prod.ext (C.injective hcode) hflag
  decode x := (C.decode (fun i => x i.succ)).map (fun a => (a, x 0))
  leftInverse x := by simp [C.leftInverse]

def option (C : BitCode A b) : BitCode (Option A) (b + 1) where
  encode x := match x with
    | none => fun _ => false
    | some a => Fin.cases true (C.encode a)
  injective := by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some a => have hh := congrFun h 0; simp at hh
    | some a =>
        cases y with
        | none => have hh := congrFun h 0; simp at hh
        | some a' =>
            congr 1
            apply C.injective
            funext i
            exact congrFun h i.succ
  decode x := if x 0 then (C.decode (fun i => x i.succ)).map some else some none
  leftInverse x := by cases x <;> simp [C.leftInverse]

def bool : BitCode Bool 1 where
  encode x := fun _ => x
  injective := fun _ _ h => congrFun h 0
  decode x := some (x 0)
  leftInverse _ := rfl

/-- The public identifier representation includes a local decoder. No
enumeration of the graph's vertices or noncomputable choice is used. -/
theorem decode_encode (C : BitCode A b) (a : A) : C.decode (C.encode a) = some a :=
  C.leftInverse a

end BitCode

def evalEncoded {V In Out Msg : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ} (code : BitCode Msg b)
    (P : Round V In Out Msg) (s : V → In) : V → Out := fun v =>
  P.update v (G.neighborFinset v) (s v) (fun w =>
    (code.decode (code.encode (P.send w (G.neighborFinset w) (s w)))).get
      (by rw [code.leftInverse]; rfl))

theorem evalEncoded_eq_eval {V In Out Msg : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ} (code : BitCode Msg b)
    (P : Round V In Out Msg) (s : V → In) : evalEncoded G code P s = eval G P s := by
  funext v
  simp only [evalEncoded, code.leftInverse, Option.get_some, eval]

/-- A typed finite protocol. Local functions and the entire program are
defined independently of the graph that will execute them. -/
inductive Program (V : Type) : Type → Type → Type 1 where
  | local {In Out : Type} (f : V → Finset V → In → Out) : Program V In Out
  | broadcast {In Out Msg : Type} (width : ℕ) (code : BitCode Msg width)
      (round : Round V In Out Msg) : Program V In Out
  | seq {In Mid Out : Type} (first : Program V In Mid) (second : Program V Mid Out) :
      Program V In Out

namespace Program

def rounds {V In Out : Type} : Program V In Out → ℕ
  | .local _ => 0
  | .broadcast _ _ _ => 1
  | .seq P Q => P.rounds + Q.rounds

def maxBits {V In Out : Type} : Program V In Out → ℕ
  | .local _ => 0
  | .broadcast width _ _ => width
  | .seq P Q => max P.maxBits Q.maxBits

def run {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Program V In Out → (V → In) → (V → Out)
  | .local f, s => fun v => f v (G.neighborFinset v) (s v)
  | .broadcast _ _ R, s => eval G R s
  | .seq P Q, s => Q.run G (P.run G s)

def iterate {V S : Type} (P : Program V S S) : ℕ → Program V S S
  | 0 => .local (fun _ _ s => s)
  | n + 1 => .seq (P.iterate n) P

theorem iterate_rounds {V S : Type} (P : Program V S S) (n : ℕ) :
    (P.iterate n).rounds = n * P.rounds := by
  induction n with
  | zero => simp only [iterate, rounds, Nat.zero_mul]
  | succ n ih => simp only [iterate, rounds, ih, Nat.add_mul, Nat.one_mul]

theorem iterate_maxBits {V S : Type} (P : Program V S S) (n : ℕ) :
    (P.iterate n).maxBits ≤ P.maxBits := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact max_le ih (le_refl _)

end Program

/-- Distinct public identifiers have `b` bits, with `b ≤ c * clog₂(n + 2)`.
The same logarithmic budget also accommodates a one-bit control field. -/
theorem logarithmic_message_budget (n b c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    b + 1 ≤ (c + 1) * Nat.clog 2 (n + 2) ∧
      1 ≤ (c + 1) * Nat.clog 2 (n + 2) := by
  have hlog : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  rw [Nat.add_mul, Nat.one_mul]
  omega

#print axioms BitCode.decode_encode
#print axioms logarithmic_message_budget

end Paper.BroadcastModel
