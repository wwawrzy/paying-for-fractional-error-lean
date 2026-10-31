import Paper.Solver.LocalSearch.GeneralCoveringParentCorrect
import Paper.Solver.LocalSearch.GeneralCoveringTerminal
import Paper.Solver.LocalSearch.ActiveSearchControl
import Paper.Solver.LocalSearch.ActiveSearchZero
import Paper.Solver.LocalSearch.RecursiveSearch

/-! A fixed bounded recursive program using private covering incidences.
The graph is used only by evaluation and correctness, never by constructors.
Physical heavy lists are a bounded superset of useful branch choices; every
residual update and terminal coverage test uses the actual covering relation. -/
namespace Paper.GeneralCoveringSearch
open BroadcastModel
variable {V : Type} [LinearOrder V]

def baseInput (B q : ℕ) : Program V (GeneralCoveringResidual.Input V B q)
    (TerminalProtocol.Input V B q) := .local fun _ _ s => s.base

def zero {b : ℕ} (C : BitCode V b) (D B q : ℕ) :=
  Program.seq (baseInput B q) (SearchCount.zero C D B q)

def control {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :=
  Program.seq (baseInput B q) (SearchControl.program C D a B q m)

def program {b : ℕ} (C : BitCode V b) (D a B q : ℕ) :
    ℕ → Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B))
  | 0 => zero C D B q
  | m + 1 => GeneralCoveringParent.program
      (GeneralCoveringTerminal.program C D B q (RecursiveSearch.threshold a (m + 1)) (m + 1))
      (control C D a B q (m + 1)) (program C D a B q m) (RecursiveSearch.branches a (m + 1))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep the continuation abstract while evaluating only the local projection. -/
theorem run_base {B q : ℕ} {Out : Type}
    (P : Program V (TerminalProtocol.Input V B q) Out)
    (s : V → GeneralCoveringResidual.Input V B q) :
    (Program.seq (baseInput B q) P).run G s = P.run G (fun v => (s v).base) := rfl

theorem zero_run {b : ℕ} (C : BitCode V b) (D B q : ℕ) (s : V → GeneralCoveringResidual.Input V B q) :
    (zero C D B q).run G s = (SearchCount.zero C D B q).run G (fun v => (s v).base) := rfl

theorem control_run {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) (s : V → GeneralCoveringResidual.Input V B q) :
    (control C D a B q m).run G s = (SearchControl.program C D a B q m).run G (fun v => (s v).base) := by
  unfold control
  exact run_base G _ s

theorem zero_correct (K : ActiveTask.Context G) (cover : V → Finset V) (B q : ℕ)
    (cost : V → Fin (B + 1)) {bits : ℕ} (C : BitCode V bits)
    (multiplicity : V → Fin (q + 1)) (s : V → GeneralCoveringResidual.Input V B q)
    (ha : ∀ v, (s v).base.active = decide (v ∈ K.vertices))
    (hb : ∀ v, (s v).base.value = multiplicity v)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0) :
    GeneralCoveringSpec.Spec cover G (zero C K.diameter B q) K.vertices cost multiplicity 0 s := by
  constructor
  · intro v hv w hw
    rw [zero_run] at hw
    obtain ⟨rfl, hcard⟩ := ActiveSearchZero.result_iff G K B q multiplicity C
      (fun u => (s u).base) ha hb v hv w hw
    have hzero := SearchZero.all_zero K.vertices multiplicity hz hcard
    refine ⟨by simp, by simp, by simp [SolutionWord.Consistent], ?_⟩
    intro r
    rw [hzero r]
    exact Nat.zero_le _
  · intro p hp _ hpc v hv
    have hp0 : ∀ u, p u = 0 := by
      intro u
      have hh : p u ≤ ∑ r, p r :=
        Finset.single_le_sum (fun r _ => Nat.zero_le (p r)) (Finset.mem_univ u)
      omega
    have hb0 : ∀ r, (multiplicity r).val = 0 := by
      intro r
      have hh := hpc r
      simpa only [hp0, Finset.sum_const_zero, Nat.le_zero_eq] using hh
    have hcard : (TerminalProtocolCorrect.demands K.vertices multiplicity).card = 0 := by
      simp [TerminalProtocolCorrect.demands, hb0]
    refine ⟨[], ?_, Nat.zero_le _⟩
    rw [zero_run, ActiveSearchCount.zero_correct G K B q multiplicity C
      (fun u => (s u).base) ha hb v hv, if_pos hcard]
  · intro v w hv hw
    rw [zero_run]
    exact ActiveSearchZero.uniform G K B q multiplicity C (fun u => (s u).base) ha hb v w hv hw

theorem correct (K : ActiveTask.Context G) (cover targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ K.vertices, cover r ⊆ SevenFoundation.closed G r)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ)) (B q : ℕ)
    (cost : V → Fin (B + 1)) {bits : ℕ} (C : BitCode V bits)
    (m : ℕ) (multiplicity : V → Fin (q + 1)) (s : V → GeneralCoveringResidual.Input V B q)
    (ha : ∀ v, (s v).base.active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).base.cost = cost v) (hb : ∀ v, (s v).base.value = multiplicity v)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0)
    (hC : ∀ r, (s r).candidates = cover r) (htarget : ∀ r, (s r).targets = targets r) :
    GeneralCoveringSpec.Spec cover G (program C K.diameter a B q m)
      K.vertices cost multiplicity m s := by
  induction m generalizing multiplicity s with
  | zero => exact zero_correct G K cover B q cost C multiplicity s ha hb hz
  | succ m ih =>
    let H := K.vertices
    let A := TerminalProtocolCorrect.demands H multiplicity
    let T := RecursiveSearch.threshold a (m + 1)
    let branchCount := RecursiveSearch.branches a (m + 1)
    let leaf := GeneralCoveringTerminal.program C K.diameter B q T (m + 1)
    let ctrl := control C K.diameter a B q (m + 1)
    let child := program C K.diameter a B q m
    change GeneralCoveringSpec.Spec cover G (GeneralCoveringParent.program leaf ctrl child branchCount)
      H cost multiplicity (m + 1) s
    refine GeneralCoveringParentCorrect.correct G cover targets H cost multiplicity s
      ha hc hb hz hC htarget leaf ctrl child ih branchCount (T ≤ A.card) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro hn
      have hsmall : A.card ≤ T := (lt_of_not_ge hn).le
      constructor
      · exact GeneralCoveringTerminal.sound G K B q T cover targets hinc cost multiplicity C s
          ha hc hb (fun v _ => htarget v) hsmall hz (m + 1)
      · intro p hp hps hpc v hv
        exact GeneralCoveringTerminal.complete G K B q T cover targets hinc cost multiplicity C s
          ha hc hb (fun v _ => htarget v) (m + 1) v hv p hp hps hpc
      · exact GeneralCoveringTerminal.uniform G K B q T targets cost multiplicity C s
          ha hc hb (fun v _ => htarget v) (m + 1)
    · intro v hv
      change ((control C K.diameter a B q (m + 1)).run G s v).large = _
      rw [control_run, ActiveSearchControl.result G K a B q (m + 1) cost multiplicity C
        (fun v => (s v).base) ha hc hb v hv]
      rfl
    · rw [show ctrl.run G s = (SearchControl.program C K.diameter a B q (m + 1)).run G
        (fun v => (s v).base) from control_run G C K.diameter a B q (m + 1) s]
      exact ActiveSearchControl.uniform G K a B q (m + 1) cost multiplicity C (fun v => (s v).base) ha hc hb
    · intro v hv
      change ∀ t ∈ ((SearchControl.program C K.diameter a B q (m + 1)).run G
        (fun v => (s v).base) v).candidates, _
      exact ActiveSearchControl.support G K a B q (m + 1) cost multiplicity C (fun v => (s v).base) ha hc hb v hv
    · intro v hv
      exact ActiveSearchControl.consistent G K a B q (m + 1) cost multiplicity C (fun v => (s v).base) ha hc hb v hv
    · intro v hv
      exact ActiveSearchControl.candidates_length G K a B q (m + 1) cost multiplicity C (fun v => (s v).base) ha hc hb v hv
    · intro hlarge p hp hps hpc v hv
      have hT : 0 < T := by dsimp [T, RecursiveSearch.threshold]; positivity
      have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hT hlarge)
      have hcover : ∀ r ∈ A, 1 ≤ ∑ u ∈ cover r, p u := by
        intro r hr
        have hh := (Finset.mem_filter.mp hr).2
        exact (by omega : 1 ≤ (multiplicity r).val).trans (hpc r)
      obtain ⟨u, hu, hpos⟩ := GeneralCoveringResidual.completion_hits_heavy G cover A hA
        (fun r hr => hlocal r (Finset.mem_filter.mp hr).1) (m + 1) (by omega) p hp hcover
      have huH : u ∈ H := by
        by_contra hn
        have hh := hps u hn
        omega
      refine ⟨CostTag.tag cost u, ?_, hpos⟩
      exact ActiveSearchControl.contains_heavy G K a B q (m + 1) cost multiplicity C
        (fun v => (s v).base) ha hc hb ha' (by omega) hden hlarge v hv u huH hu
end Paper.GeneralCoveringSearch

#print axioms Paper.GeneralCoveringSearch.zero_correct
#print axioms Paper.GeneralCoveringSearch.correct
