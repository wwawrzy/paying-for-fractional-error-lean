import Paper.Solver.Density.CappedCompletion
import Paper.Solver.Density.CappedOutputRegister

/-! Correctness of irrevocable local output registers in the encoded
protocol. Every register records exactly the first successful probe and
retains that answer. No global degree or stopping time is a protocol input. -/
namespace Paper.Density.CappedRegisteredCompletion
open SevenFoundation
open CappedCompletion (observed firstTime)
open CappedOutputRegister (latch before reported)
open CappedUniformParameters (rho)
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
include hc hm

theorem before_none (v : V) (n : ℕ) (hn : n ≤ firstTime G p cap hc hm v) :
    before G cap m (rho m) n v = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change latch (before G cap m (rho m) n v) (observed G cap m n v) = none
    rw [ih (by omega)]
    have hnfalse := CappedCompletion.before_firstTime G p cap hc hm v (n := n) (by omega)
    simp only [latch, if_neg hnfalse]

theorem reported_at_first (v : V) :
    reported G cap m (rho m) (firstTime G p cap hc hm v) v =
      some (observed G cap m (firstTime G p cap hc hm v) v).output := by
  change latch (before G cap m (rho m) (firstTime G p cap hc hm v) v) _ = _
  rw [before_none G p cap hc hm v _ le_rfl]
  change (if (observed G cap m (firstTime G p cap hc hm v) v).done then
    some (observed G cap m (firstTime G p cap hc hm v) v).output else none) = _
  rw [CappedCompletion.firstTime_done G p cap hc hm v]
  rfl

theorem reported_after (v : V) (k : ℕ) :
    reported G cap m (rho m) (firstTime G p cap hc hm v + k) v =
      some (observed G cap m (firstTime G p cap hc hm v) v).output := by
  induction k with
  | zero => exact reported_at_first G p cap hc hm v
  | succ k ih =>
    change latch (reported G cap m (rho m) (firstTime G p cap hc hm v + k) v) _ = _
    rw [ih]
    rfl

theorem actual_local_output (v : V) (n : ℕ) (hn : firstTime G p cap hc hm v ≤ n) :
    ((CappedOutputRegister.schedule cap m (rho m) n).run G (fun _ => PUnit.unit) v).2 =
      some (observed G cap m (firstTime G p cap hc hm v) v).output := by
  rw [CappedOutputRegister.schedule_run]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact reported_after G p cap hc hm v k

theorem actual_output_eq (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) :
    Finset.univ.filter (fun v =>
      ((CappedOutputRegister.schedule cap m (rho m) (CappedGrowth.timeBound m Delta)).run G
        (fun _ => PUnit.unit) v).2 = some true) = CappedCompletion.output G p cap hc hm := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CappedCompletion.output]
  rw [actual_local_output G p cap hc hm v _
    (CappedCompletion.firstTime_le G p cap hc hm Delta hdegree v)]
  simp only [Option.some.injEq]

/-- The actual output registers all hold final answers by the analysis
deadline, and those answers have the exact domination guarantee. -/
theorem domination_bound (hden : Incidence.InducedDensityBound G p.a)
    (hrho : 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) :
    let D := Finset.univ.filter (fun v =>
      ((CappedOutputRegister.schedule cap m (rho m) (CappedGrowth.timeBound m Delta)).run G
        (fun _ => PUnit.unit) v).2 = some true)
    dominates G D ∧ (D.card : ℝ) ≤ (2*p.a+1)*fractionalNumber G := by
  dsimp only
  rw [actual_output_eq G p cap hc hm Delta hdegree]
  exact CappedCompletion.domination_bound G p cap hc hm hden hrho

end Paper.Density.CappedRegisteredCompletion
#print axioms Paper.Density.CappedRegisteredCompletion.actual_local_output
#print axioms Paper.Density.CappedRegisteredCompletion.domination_bound
