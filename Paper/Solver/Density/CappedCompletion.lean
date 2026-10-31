import Paper.Solver.Density.CappedExecution
import Paper.Solver.Density.CappedHaltRounds
import Paper.Solver.Density.CappedUniformParameters

/-! Local output completion of the encoded capped execution. The first
successful probe is an analysis index of a local Boolean stopping rule;
it is not a degree bound or a horizon supplied to the algorithm. Different
vertices can complete at different indices, with the same final guarantee. -/
namespace Paper.Density.CappedCompletion
open SevenFoundation
open CappedCounterState (decode)
open CappedUniformParameters (rho)
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def observed (cap : ℚ) (m n : ℕ) : V → CappedHaltRounds.Result :=
  CappedHaltRounds.probe G cap m (rho m) (CappedExecution.run G cap m (rho m) n)

variable (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
include hc hm

theorem decoded_state (n : ℕ) :
    (fun v => (decode cap m (CappedExecution.run G cap m (rho m) n v) : ℝ)) =
      CappedConvergence.state G p m n := by
  have hp : (0 : ℝ) ≤ (cap : ℝ) := hc.symm ▸ (CappedConvergence.cap_bounds p).1.le
  have hpq : 0 ≤ cap := by exact_mod_cast hp
  rw [CappedExecution.run_cast G cap hm hpq, hc,
    CappedUniformParameters.scale_cast, CappedUniformParameters.rho_cast]
  rfl

theorem observed_output (n : ℕ) (v : V) :
    (observed G cap m n v).output = CappedLocalHalt.outputBit G (CappedGrowth.rho m)
      (CappedConvergence.state G p m n) v := by
  unfold observed
  rw [CappedHaltRounds.probe_output, decoded_state G p cap hc hm,
    CappedUniformParameters.rho_cast]

theorem observed_done (n : ℕ) (v : V) :
    (observed G cap m n v).done = true ↔
      CappedLocalHalt.certificate G (CappedConvergence.cap p) (CappedGrowth.rho m)
        (CappedConvergence.state G p m n) v := by
  unfold observed
  rw [CappedHaltRounds.probe_done_iff, decoded_state G p cap hc hm,
    hc, CappedUniformParameters.rho_cast]

theorem done_at_bound (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    (observed G cap m (CappedGrowth.timeBound m Delta) v).done = true :=
  (observed_done G p cap hc hm _ v).mpr
    (CappedConvergence.local_certificate G p hm Delta hdegree v)

theorem output_stable (n k : ℕ) (v : V)
    (hdone : (observed G cap m n v).done = true) :
    (observed G cap m (n+k) v).output = (observed G cap m n v).output := by
  rw [observed_output G p cap hc hm, observed_output G p cap hc hm]
  exact CappedLocalHalt.certified_output_stable G
    (CappedConvergence.cap_bounds p).1.le (CappedGrowth.factor_bounds hm).1.le
    (CappedGrowth.factor_mul_rho hm).le
    (CappedInitialization.initial G (CappedConvergence.cap p))
    (fun v => (CappedInitialization.initial_pos G (CappedConvergence.cap_bounds p).1 v).le)
    (CappedInitialization.initial_le_cap G _) (CappedInitialization.initial_packing G _)
    n k v ((observed_done G p cap hc hm n v).mp hdone)

theorem completion_exists (v : V) : ∃ n, (observed G cap m n v).done = true := by
  refine ⟨CappedGrowth.timeBound m (Fintype.card V),
    done_at_bound G p cap hc hm _ ?_ v⟩
  intro u
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_le_univ (G.neighborFinset u)

/-- The first successful local probe, defined only for analysis. -/
noncomputable def firstTime (v : V) : ℕ :=
  Nat.find (completion_exists G p cap hc hm v)

theorem firstTime_done (v : V) :
    (observed G cap m (firstTime G p cap hc hm v) v).done = true :=
  Nat.find_spec (completion_exists G p cap hc hm v)

theorem before_firstTime (v : V) {n : ℕ} (hn : n < firstTime G p cap hc hm v) :
    (observed G cap m n v).done ≠ true :=
  Nat.find_min (completion_exists G p cap hc hm v) hn

theorem firstTime_le (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    firstTime G p cap hc hm v ≤ CappedGrowth.timeBound m Delta :=
  Nat.find_min' (completion_exists G p cap hc hm v)
    (done_at_bound G p cap hc hm Delta hdegree v)

theorem first_output_eq (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    (observed G cap m (firstTime G p cap hc hm v) v).output =
      (observed G cap m (CappedGrowth.timeBound m Delta) v).output := by
  have hle := firstTime_le G p cap hc hm Delta hdegree v
  have h := output_stable G p cap hc hm (firstTime G p cap hc hm v)
    (CappedGrowth.timeBound m Delta - firstTime G p cap hc hm v) v
    (firstTime_done G p cap hc hm v)
  rw [Nat.add_sub_of_le hle] at h
  exact h.symm

/-- Each membership bit is taken at that vertex's own first completion. -/
noncomputable def output : Finset V :=
  Finset.univ.filter (fun v =>
    (observed G cap m (firstTime G p cap hc hm v) v).output = true)

theorem output_eq (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) :
    output G p cap hc hm = CappedSelection.output G
      (CappedConvergence.selected G (CappedGrowth.rho m)
        (CappedConvergence.state G p m (CappedGrowth.timeBound m Delta))) := by
  ext v
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [first_output_eq G p cap hc hm Delta hdegree,
    observed_output G p cap hc hm, CappedConvergence.output_membership]

/-- The exact coefficient holds for the locally completed output, not just
for a vector sampled at a globally supplied stopping horizon. -/
theorem domination_bound (hden : Incidence.InducedDensityBound G p.a)
    (hrho : 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m) :
    dominates G (output G p cap hc hm) ∧
      ((output G p cap hc hm).card : ℝ) ≤ (2*p.a+1)*fractionalNumber G := by
  have hdegree : ∀ v, G.degree v ≤ Fintype.card V := by
    intro v
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      Finset.card_le_univ (G.neighborFinset v)
  rw [output_eq G p cap hc hm (Fintype.card V) hdegree]
  exact CappedConvergence.domination_bound G p hden hm hrho _ hdegree

end Paper.Density.CappedCompletion
#print axioms Paper.Density.CappedCompletion.output_stable
#print axioms Paper.Density.CappedCompletion.firstTime_le
#print axioms Paper.Density.CappedCompletion.domination_bound
