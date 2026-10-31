import Paper.Communication.PortBroadcastModel

/-! Standard deterministic LOCAL: own ID, degree, neighbor IDs by local port
(KT1); arbitrary message types, separate message for each outgoing port.
The network and its reverse-port map occur only in the evaluator. -/
namespace Paper.PortLocal

structure Context (degree : ℕ) where
  ident : ℕ
  neighbors : Fin degree → ℕ

structure Round (In Out Msg : Type) where
  send : (degree : ℕ) → Context degree → In → Fin degree → Msg
  update : (degree : ℕ) → Context degree → In → (Fin degree → Msg) → Out

inductive Program : Type → Type → Type 1 where
  | local {In Out : Type} (f : (degree : ℕ) → Context degree → In → Out) : Program In Out
  | round {In Out Msg : Type} (R : Round In Out Msg) : Program In Out
  | seq {In Mid Out : Type} (P : Program In Mid) (Q : Program Mid Out) : Program In Out

structure Network (V : Type) where
  degree : V → ℕ
  neighbor : (v : V) → Fin (degree v) → V
  back : (v : V) → (p : Fin (degree v)) → Fin (degree (neighbor v p))
  reverse_neighbor : ∀ v p, neighbor (neighbor v p) (back v p) = v

namespace Network

def context {V : Type} (N : Network V) (ids : V → ℕ) (v : V) : Context (N.degree v) :=
  ⟨ids v, fun p => ids (N.neighbor v p)⟩

def Compatible {V : Type} (N : Network V) (G : SimpleGraph V) : Prop :=
  (∀ v, Function.Injective (N.neighbor v)) ∧
  ∀ v w, G.Adj v w ↔ ∃ p, N.neighbor v p = w

/-- Every ordinary numbering of the physical graph gives this evaluator. -/
def ofNumbering {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ports : PortBroadcastModel.Numbering G) : Network V where
  degree := fun v => G.degree v
  neighbor v p := (ports v p).val
  back v p := (ports (ports v p).val).symm ⟨v, by
    apply (G.mem_neighborFinset _ _).mpr
    exact ((G.mem_neighborFinset _ _).mp (ports v p).property).symm⟩
  reverse_neighbor v p := by simp

theorem ofNumbering_compatible {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ports : PortBroadcastModel.Numbering G) :
    (ofNumbering G ports).Compatible G := by
  constructor
  · intro v p q h
    exact (ports v).injective (Subtype.ext h)
  · intro v w
    constructor
    · intro h
      exact ⟨(ports v).symm ⟨w, (G.mem_neighborFinset _ _).mpr h⟩, by simp [ofNumbering]⟩
    · rintro ⟨p, rfl⟩
      exact (G.mem_neighborFinset _ _).mp (ports v p).property

end Network

namespace Program

def run {V : Type} {In Out : Type} (N : Network V) (ids : V → ℕ) :
    Program In Out → (V → In) → V → Out
  | .local f, s => fun v => f (N.degree v) (N.context ids v) (s v)
  | .round R, s => fun v => R.update (N.degree v) (N.context ids v) (s v) (fun p =>
      R.send (N.degree (N.neighbor v p)) (N.context ids (N.neighbor v p)) (s (N.neighbor v p)) (N.back v p))
  | .seq P Q, s => Q.run N ids (P.run N ids s)

def rounds {In Out : Type} : Program In Out → ℕ
  | .local _ => 0
  | .round _ => 1
  | .seq P Q => P.rounds+Q.rounds

end Program
end Paper.PortLocal
