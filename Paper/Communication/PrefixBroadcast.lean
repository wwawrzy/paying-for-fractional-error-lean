import Paper.Communication.PrefixCode

/-! Graph-independent finite-string broadcasts. Message lengths are bounded
on reachable states, without providing an analysis bound to the encoder. -/
namespace Paper.PrefixBroadcast
open BroadcastModel

def round {V In Out Msg : Type} [Inhabited Msg]
    (C : PrefixCode Msg) (P : Round V In Out Msg) : Round V In Out (List Bool) where
  send v N s := C.encode (P.send v N s)
  update v N s messages := P.update v N s (fun u => (C.decode (messages u)).getD default)

theorem eval_eq {V In Out Msg : Type} [Fintype V] [DecidableEq V] [Inhabited Msg]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : PrefixCode Msg)
    (P : Round V In Out Msg) (s : V → In) :
    eval G (round C P) s = eval G P s := by
  funext v
  simp only [eval, round, PrefixCode.decode_encode, Option.getD_some]

theorem sent_length {V In Out Msg : Type} [Inhabited Msg]
    (C : PrefixCode Msg) (P : Round V In Out Msg) (v : V) (N : Finset V) (s : In) :
    ((round C P).send v N s).length = (C.encode (P.send v N s)).length := rfl

end Paper.PrefixBroadcast
#print axioms Paper.PrefixBroadcast.eval_eq
