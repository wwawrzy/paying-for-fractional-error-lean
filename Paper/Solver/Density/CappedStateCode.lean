import Paper.Communication.PrefixBroadcast
import Paper.Solver.Density.CappedCounterState
import Paper.Solver.Density.CappedMessageBounds

/-! The actual finite-string codec for capped-state broadcasts. It is
independent of the graph, its order, its degree and the execution horizon. -/
namespace Paper.Density.CappedStateCode
open CappedCounterState

instance : Inhabited State := ⟨⟨0,0,false⟩⟩

def code : PrefixCode State where
  encode s := PrefixCode.counters.encode (s.denominator,s.exponent,s.capped)
  read bits := (PrefixCode.counters.read bits).map fun p =>
    (⟨p.1.1,p.1.2.1,p.1.2.2⟩,p.2)
  read_append s tail := by
    simp only [PrefixCode.read_append, Option.map_some]

theorem decode_encode (s : State) : code.decode (code.encode s) = some s :=
  code.decode_encode s

theorem logarithmic_length (m Delta vertices extra : ℕ) (s : State)
    (hdegree : Delta ≤ vertices) (hden : s.denominator ≤ Delta+1)
    (hexponent : s.exponent ≤ CappedGrowth.timeBound m Delta + extra) :
    (code.encode s).length ≤ (2*m+2*extra+5)*Nat.clog 2 (vertices+2) :=
  CappedMessageBounds.logarithmic_packets m Delta vertices extra s.denominator s.exponent
    s.capped hdegree hden hexponent

theorem encoded_round_eq {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : BroadcastModel.Round V In Out State) (s : V → In) :
    BroadcastModel.eval G (PrefixBroadcast.round code P) s = BroadcastModel.eval G P s :=
  PrefixBroadcast.eval_eq G code P s

end Paper.Density.CappedStateCode
#print axioms Paper.Density.CappedStateCode.decode_encode
#print axioms Paper.Density.CappedStateCode.logarithmic_length
#print axioms Paper.Density.CappedStateCode.encoded_round_eq
