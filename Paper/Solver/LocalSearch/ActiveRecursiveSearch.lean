import Paper.Solver.LocalSearch.RecursiveSearchCorrect
import Paper.Preliminaries.ActiveTerminalWord
import Paper.Solver.LocalSearch.ActiveSearchZero
import Paper.Solver.LocalSearch.ActiveSearchControl

/-! Full budget induction for the actual recursive solver on arbitrary
nonempty active tasks with proved induced diameter. No solver oracle. -/
namespace Paper.ActiveRecursiveSearch
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (K : ActiveTask.Context G) (a : ℕ) (ha' : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (B q : ℕ)
    (cost : V → Fin (B + 1)) {bits : ℕ} (C : BitCode V bits)
    (m : ℕ) (multiplicity : V → Fin (q + 1)) (s : V → TerminalProtocol.Input V B q)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0) :
    SearchSpec.Spec G (RecursiveSearch.program C K.diameter a B q m)
      K.vertices cost multiplicity m s := by
  induction m generalizing multiplicity s with
  | zero =>
    constructor
    · exact ActiveSearchZero.sound G K B q cost multiplicity C s ha hb hz
    · intro p hp _ hpc v hv
      exact ActiveSearchZero.complete G K B q cost multiplicity C s ha hb v hv p hp hpc
    · exact ActiveSearchZero.uniform G K B q multiplicity C s ha hb
  | succ m ih =>
    let H := K.vertices
    let A := TerminalProtocolCorrect.demands H multiplicity
    let T := RecursiveSearch.threshold a (m + 1)
    let branchCount := RecursiveSearch.branches a (m + 1)
    let leaf := TerminalWord.program C K.diameter B q T (m + 1)
    let control := SearchControl.program C K.diameter a B q (m + 1)
    let child := RecursiveSearch.program C K.diameter a B q m
    change SearchSpec.Spec G (BranchParent.program leaf control child branchCount) H cost multiplicity (m + 1) s
    refine SearchParentCorrect.correct G H cost multiplicity s ha hc hb hz leaf control child ih
      branchCount (T ≤ A.card) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro hn
      have hsmall : A.card ≤ T := (lt_of_not_ge hn).le
      constructor
      · exact ActiveTerminalWord.sound G K B q T cost multiplicity C s ha hc hb hsmall hz (m + 1)
      · intro p hp hps hpc v hv
        exact ActiveTerminalWord.complete G K B q T cost multiplicity C s ha hc hb
          (m + 1) v hv p hp hps hpc
      · exact ActiveTerminalWord.uniform G K B q T cost multiplicity C s ha hc hb (m + 1)
    · intro v hv
      change ((SearchControl.program C K.diameter a B q (m + 1)).run G s v).large = _
      rw [ActiveSearchControl.result G K a B q (m + 1) cost multiplicity C s ha hc hb v hv]
      rfl
    · exact ActiveSearchControl.uniform G K a B q (m + 1) cost multiplicity C s ha hc hb
    · exact ActiveSearchControl.support G K a B q (m + 1) cost multiplicity C s ha hc hb
    · exact ActiveSearchControl.consistent G K a B q (m + 1) cost multiplicity C s ha hc hb
    · exact ActiveSearchControl.candidates_length G K a B q (m + 1) cost multiplicity C s ha hc hb
    · intro hlarge p hp hps hpc v hv
      have hT : 0 < T := by dsimp [T, RecursiveSearch.threshold]; positivity
      have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hT hlarge)
      have hcover : ∀ r ∈ A, 1 ≤ ∑ u ∈ SevenFoundation.closed G r, p u := by
        intro r hr
        have hh := (Finset.mem_filter.mp hr).2
        exact (by omega : 1 ≤ (multiplicity r).val).trans (hpc r)
      obtain ⟨u, hu, hpos⟩ := LocalSearchBounds.completion_hits_heavy G A hA (m + 1) (by omega) p hp hcover
      have huH : u ∈ H := by
        by_contra hn
        have hh := hps u hn
        omega
      refine ⟨CostTag.tag cost u, ?_, hpos⟩
      exact ActiveSearchControl.contains_heavy G K a B q (m + 1) cost multiplicity C s
        ha hc hb ha' (by omega) hden hlarge v hv u huH hu
end Paper.ActiveRecursiveSearch
