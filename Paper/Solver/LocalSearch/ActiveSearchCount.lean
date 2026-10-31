import Paper.Solver.LocalSearch.SearchCount
import Paper.Averaging.Tasks.ActiveTaskContext

/-! Actual search count and zero-case result on arbitrary active task geometry. -/
namespace Paper.ActiveSearchCount
open BroadcastModel SearchCount
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q : ℕ) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hb : ∀ v, (s v).value = multiplicity v)
include ha hb

theorem correct (v : V) (hv : v ∈ K.vertices) :
    (program C K.diameter B q).run G s v = some
      (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card := by
  let H := K.vertices
  let A := TerminalProtocolCorrect.demands H multiplicity
  have hi : (fun u => queryInput b (s u)) = fun u => (decide (u ∈ H),
      fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0)) := by
    funext u
    dsimp only [queryInput]
    rw [ha u, hb u]
    apply Prod.ext
    · rfl
    · funext i
      simp [A, H, TerminalProtocolCorrect.demands]
  have hcounts := ActiveTaskQueries.counts G C K.vertices K.nonempty K.diameter 1 K.paths (fun _ => A)
    (fun _ => Finset.filter_subset _ _) v hv
  have hh := congrArg (Option.map (fun f : Fin 1 → ℕ => f 0)) hcounts
  simp only [Option.map_map, Option.map_some] at hh
  change (((TaskQueries.countProgram C 1 K.diameter).run G
    (fun u => (decide (u ∈ H), fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0))) v).2.map
      (fun f => (f 0).value.val)) = some A.card at hh
  rw [run_program, hi]
  exact hh

theorem zero_correct (v : V) (hv : v ∈ K.vertices) :
    (zero C K.diameter B q).run G s v =
      if (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card = 0
      then some [] else none := by
  change (match (program C K.diameter B q).run G s v with
    | some 0 => some ([] : SolutionWord.Word V B)
    | _ => none) = _
  rw [correct G K B q multiplicity C s ha hb v hv]
  cases hn : (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card <;>
    simp [hn]

end Paper.ActiveSearchCount
