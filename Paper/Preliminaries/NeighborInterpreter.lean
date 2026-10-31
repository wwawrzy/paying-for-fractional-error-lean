import Paper.Communication.BroadcastModel
import Paper.Partitions.Local.NeighborBalls

/-! A computable local interpreter from finite received neighbor records.
It never enumerates V or needs Fintype V/graph adjacency. Missing records
can be given any fixed finite-neighbor default; locality is proved later. -/
namespace Paper.NeighborInterpreter
open BroadcastModel
variable {V : Type} [DecidableEq V]

def run (N : V → Finset V) {In Out : Type} : Program V In Out → (V → In) → V → Out
  | .local f, s => fun v => f v (N v) (s v)
  | .broadcast _ _ R, s => fun v => R.update v (N v) (s v) (fun u => R.send u.val (N u.val) (s u.val))
  | .seq P Q, s => run N Q (run N P s)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_graph {In Out : Type} (P : Program V In Out) : ∀ s : V → In,
    run (fun v => G.neighborFinset v) P s = P.run G s := by
  induction P with
  | «local» f => intro s; rfl
  | broadcast w code R => intro s; rfl
  | seq P Q ihP ihQ =>
    intro s
    change run _ Q (run _ P s) = _
    rw [ihP s]
    exact ihQ _
end Paper.NeighborInterpreter
