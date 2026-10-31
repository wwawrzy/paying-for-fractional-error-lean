import Paper.Communication.BroadcastModel

namespace Paper.BroadcastModel.Program

def runEncoded {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Program V In Out → (V → In) → (V → Out)
  | .local f, s => fun v => f v (G.neighborFinset v) (s v)
  | .broadcast _ code R, s => evalEncoded G code R s
  | .seq P Q, s => Q.runEncoded G (P.runEncoded G s)

theorem runEncoded_eq_run {V In Out : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Program V In Out) (s : V → In) :
    P.runEncoded G s = P.run G s := by
  induction P with
  | «local» f => rfl
  | broadcast b code R => exact evalEncoded_eq_eval G code R s
  | seq P Q ihP ihQ => simp only [runEncoded, run, ihP, ihQ]

#print axioms runEncoded_eq_run

end Paper.BroadcastModel.Program
