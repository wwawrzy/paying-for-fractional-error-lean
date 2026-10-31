import Paper.Communication.BroadcastModel

/-! A KT0 broadcast model. A local instruction receives own identifier,
own degree, own state and messages indexed by local ports. No instruction
receives neighboring identifiers. Numberings appear only in the evaluator. -/
namespace Paper.PortBroadcastModel
open BroadcastModel (BitCode)

structure Round (V In Out Msg : Type) where
  send : V → ℕ → In → Msg
  update : V → (degree : ℕ) → In → (Fin degree → Msg) → Out

inductive Program (V : Type) : Type → Type → Type 1 where
  | local {In Out : Type} (f : V → ℕ → In → Out) : Program V In Out
  | broadcast {In Out Msg : Type} (width : ℕ) (code : BitCode Msg width)
      (round : Round V In Out Msg) : Program V In Out
  | seq {In Mid Out : Type} (P : Program V In Mid) (Q : Program V Mid Out) : Program V In Out

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Numbering := ∀ v : V, Fin (G.degree v) ≃ ↥(G.neighborFinset v)

theorem numbering_exists : Nonempty (Numbering G) := by
  classical
  refine ⟨fun v => ?_⟩
  have he : Fintype.card ↥(G.neighborFinset v) = G.degree v := by simp only [Fintype.card_coe]; rfl
  exact (Fintype.equivFinOfCardEq he).symm

def eval {In Out Msg : Type} (ports : Numbering G) (R : Round V In Out Msg)
    (s : V → In) : V → Out := fun v => R.update v (G.degree v) (s v)
      (fun i => R.send (ports v i).val (G.degree (ports v i).val) (s (ports v i).val))

def evalEncoded {In Out Msg : Type} (ports : Numbering G) {b : ℕ} (C : BitCode Msg b)
    (R : Round V In Out Msg) (s : V → In) : V → Out := fun v =>
  R.update v (G.degree v) (s v) (fun i =>
    (C.decode (C.encode (R.send (ports v i).val (G.degree (ports v i).val) (s (ports v i).val)))).get
      (by rw [C.leftInverse]; rfl))

theorem evalEncoded_eq_eval {In Out Msg : Type} (ports : Numbering G) {b : ℕ} (C : BitCode Msg b)
    (R : Round V In Out Msg) (s : V → In) : evalEncoded G ports C R s = eval G ports R s := by
  funext v
  simp only [evalEncoded, C.leftInverse, Option.get_some, eval]

namespace Program

def run {In Out : Type} (ports : Numbering G) : Program V In Out → (V → In) → V → Out
  | .local f, s => fun v => f v (G.degree v) (s v)
  | .broadcast _ _ R, s => eval G ports R s
  | .seq P Q, s => Q.run ports (P.run ports s)

def runEncoded {In Out : Type} (ports : Numbering G) : Program V In Out → (V → In) → V → Out
  | .local f, s => fun v => f v (G.degree v) (s v)
  | .broadcast _ C R, s => evalEncoded G ports C R s
  | .seq P Q, s => Q.runEncoded ports (P.runEncoded ports s)

theorem runEncoded_eq_run {In Out : Type} (ports : Numbering G) (P : Program V In Out) (s : V → In) :
    P.runEncoded G ports s = P.run G ports s := by
  induction P with
  | «local» f => rfl
  | broadcast b C R => exact evalEncoded_eq_eval G ports C R s
  | seq P Q ihP ihQ => simp only [runEncoded, run, ihP, ihQ]

def rounds {W In Out : Type} : Program W In Out → ℕ
  | .local _ => 0
  | .broadcast _ _ _ => 1
  | .seq P Q => P.rounds + Q.rounds

def maxBits {W In Out : Type} : Program W In Out → ℕ
  | .local _ => 0
  | .broadcast b _ _ => b
  | .seq P Q => max P.maxBits Q.maxBits

end Program
end Paper.PortBroadcastModel
