import Paper.Communication.PrefixBroadcast

/-! Finite schedules of graph-independent, finite-string broadcasts.
Message widths are measured on the executed states, rather than given as
public encoder parameters. This permits uniform unknown-degree protocols. -/
namespace Paper.PrefixBroadcast
open BroadcastModel (Round eval)

inductive Program (V : Type) : Type → Type → Type 1 where
  | local {In Out : Type} (f : V → Finset V → In → Out) : Program V In Out
  | broadcast {In Out : Type} (P : Round V In Out (List Bool)) : Program V In Out
  | seq {In Mid Out : Type} (first : Program V In Mid) (second : Program V Mid Out) :
      Program V In Out

namespace Program

def rounds {V In Out : Type} : Program V In Out → ℕ
  | .local _ => 0
  | .broadcast _ => 1
  | .seq P Q => P.rounds + Q.rounds

def run {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Program V In Out → (V → In) → (V → Out)
  | .local f, s => fun v => f v (G.neighborFinset v) (s v)
  | .broadcast P, s => eval G P s
  | .seq P Q, s => Q.run G (P.run G s)

def maxBits {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Program V In Out → (V → In) → ℕ
  | .local _, _ => 0
  | .broadcast P, s => Finset.univ.sup (fun v => (P.send v (G.neighborFinset v) (s v)).length)
  | .seq P Q, s => max (P.maxBits G s) (Q.maxBits G (P.run G s))

theorem broadcast_bits_le {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Round V In Out (List Bool))
    (s : V → In) (b : ℕ)
    (h : ∀ v, (P.send v (G.neighborFinset v) (s v)).length ≤ b) :
    (broadcast P).maxBits G s ≤ b := Finset.sup_le (fun v _ => h v)

theorem seq_bits_le {V In Mid Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Program V In Mid) (Q : Program V Mid Out)
    (s : V → In) (b : ℕ) (hP : P.maxBits G s ≤ b) (hQ : Q.maxBits G (P.run G s) ≤ b) :
    (seq P Q).maxBits G s ≤ b := max_le hP hQ

def iterate {V S : Type} (P : Program V S S) : ℕ → Program V S S
  | 0 => .local (fun _ _ s => s)
  | n+1 => .seq (P.iterate n) P

theorem iterate_rounds {V S : Type} (P : Program V S S) (n : ℕ) :
    (P.iterate n).rounds = n*P.rounds := by
  induction n with
  | zero => simp only [iterate, rounds, Nat.zero_mul]
  | succ n ih => simp only [iterate, rounds, ih, Nat.add_mul, Nat.one_mul]

theorem iterate_run_succ {V S : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Program V S S) (n : ℕ) (s : V → S) :
    (P.iterate (n+1)).run G s = P.run G ((P.iterate n).run G s) := rfl

end Program
end Paper.PrefixBroadcast
#print axioms Paper.PrefixBroadcast.Program.broadcast_bits_le
#print axioms Paper.PrefixBroadcast.Program.seq_bits_le
#print axioms Paper.PrefixBroadcast.Program.iterate_rounds
