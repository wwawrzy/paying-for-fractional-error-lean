import Paper.Preliminaries.DemandValues
import Paper.Averaging.Tasks.ActiveTaskContext

/-! Actual residual-demand value queries on arbitrary active task geometry. -/
namespace Paper.ActiveDemandValues
open BroadcastModel DemandValues CappedCount
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (K : ActiveTask.Context G)

theorem correct {b : ℕ} (C : BitCode V b)
    (q T : ℕ) (l : List V)
    (multiplicity : V → Fin (q + 1)) (s : V → Input V q)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hb : ∀ v, (s v).value = multiplicity v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l)
    (hlist : ∀ r ∈ l, r ∈ K.vertices) :
    ∀ v ∈ K.vertices,
      ((program C K.diameter q T).run G s v).2 = some (values T l multiplicity) := by
  let H := K.vertices
  have hz : ∀ v, v ∉ H → weights H q T l multiplicity v = 0 := by
    intro v hv
    funext i
    simp [weights, hv]
  intro v hv
  have hi := input_eq H q T l multiplicity s ha hb hl
  have hres := ActiveTaskQueries.allReduce G C (PacketCode.vector (code q) T) K.vertices K.nonempty K.diameter K.paths (weights H q T l multiplicity) hz v hv
  rw [run_program, hi]
  dsimp only
  rw [hres, Option.map_some, sum_weights H q T l multiplicity hlist]
  exact congrArg some (decoded_values q T l multiplicity)

end Paper.ActiveDemandValues
