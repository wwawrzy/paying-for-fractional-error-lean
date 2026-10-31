import Paper.Solver.Density.CappedSelection
import Paper.Solver.Density.CappedInitialization
import Paper.Solver.Density.CappedGrowth
import Paper.Solver.Density.CappedLocalHalt

/-! Convergence of the actual locally initialized capped recurrence and its
exact domination guarantee. The degree bound occurs only in analysis time.
Finite-message implementation is a separate obligation. -/
namespace Paper.Density.CappedConvergence
open SevenFoundation
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def selected (rho : ℝ) (y : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => rho ≤ UnitDomination.mass G y v)

theorem blocked_iff_covered (rho : ℝ) (y : V → ℝ) (v : V) :
    CappedDynamics.blocked G rho y v ↔ v ∈ covered G (selected G rho y) := by
  constructor
  · rintro ⟨r, hr, ht⟩
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩,
      (closed_symm G v r).mpr hr⟩
  · intro hv
    obtain ⟨r, hr, hv⟩ := Finset.mem_biUnion.mp hv
    exact ⟨r, (closed_symm G v r).mp hv, (Finset.mem_filter.mp hr).2⟩

theorem output_membership (rho : ℝ) (y : V → ℝ) (v : V) :
    v ∈ CappedSelection.output G (selected G rho y) ↔
      CappedLocalHalt.outputBit G rho y v = true := by
  simp only [CappedSelection.output, CappedSelection.residual, Finset.mem_union,
    selected, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    CappedLocalHalt.outputBit, decide_eq_true_eq]
  rw [blocked_iff_covered]
  rfl

/-- The integer growth parameter is chosen before every graph. -/
theorem parameters (p : NeighborhoodSlack.Parameters) :
    ∃ m : ℕ, 0 < m ∧ 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m := by
  let b := 2*p.a+1
  let e := NeighborhoodSlack.eta p
  have hb : 0 < b := by dsimp [b]; linarith [p.a_ge_one]
  have he : 0 < e := NeighborhoodSlack.eta_pos p
  obtain ⟨m, hm⟩ := exists_nat_gt (b/e)
  have hmpos : 0 < m := by
    have hh : (0 : ℝ) < m := (div_pos hb he).trans hm
    exact_mod_cast hh
  refine ⟨m, hmpos, ?_⟩
  have hme : b < (m : ℝ)*e := (div_lt_iff₀ he).mp hm
  have hd : (0 : ℝ) < (m : ℝ)+1 := by positivity
  change b-e ≤ b*((m : ℝ)/((m : ℝ)+1))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  nlinarith

noncomputable def cap (p : NeighborhoodSlack.Parameters) : ℝ := 1/(2*p.a+1)

theorem cap_bounds (p : NeighborhoodSlack.Parameters) : 0 < cap p ∧ cap p ≤ 1 := by
  have hb : 1 ≤ 2*p.a+1 := by linarith [p.a_ge_one]
  exact ⟨one_div_pos.mpr (by linarith), (one_div_le_one_div_of_le zero_lt_one hb).trans_eq (by norm_num)⟩

noncomputable def state (p : NeighborhoodSlack.Parameters) (m n : ℕ) : V → ℝ :=
  CappedDynamics.run G (cap p) (CappedGrowth.factor m) (CappedGrowth.rho m)
    (CappedInitialization.initial G (cap p)) n

theorem state_invariant (p : NeighborhoodSlack.Parameters) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∀ v, 0 ≤ state G p m n v) ∧ (∀ v, state G p m n v ≤ cap p) ∧
      (∀ v, UnitDomination.mass G (state G p m n) v ≤ 1) :=
  CappedDynamics.run_invariant G (cap_bounds p).1.le (CappedGrowth.factor_bounds hm).1.le
    (CappedGrowth.factor_mul_rho hm).le _
    (fun v => (CappedInitialization.initial_pos G (cap_bounds p).1 v).le)
    (CappedInitialization.initial_le_cap G _) (CappedInitialization.initial_packing G _) n

theorem terminal (p : NeighborhoodSlack.Parameters) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    CappedDynamics.blocked G (CappedGrowth.rho m) (state G p m (CappedGrowth.timeBound m Delta)) v ∨
      state G p m (CappedGrowth.timeBound m Delta) v = cap p := by
  apply CappedDynamics.terminal_of_growth G (cap_bounds p).1.le
    (CappedGrowth.factor_bounds hm).1.le (CappedGrowth.factor_mul_rho hm).le
    (CappedInitialization.initial G (cap p))
    (fun v => (CappedInitialization.initial_pos G (cap_bounds p).1 v).le)
    (CappedInitialization.initial_le_cap G _) (CappedInitialization.initial_packing G _)
  intro u
  exact CappedGrowth.cap_le_grown hm Delta (cap_bounds p).1 (cap_bounds p).2
    (CappedInitialization.initial_lower_bound G _ hdegree u)

/-- No terminal packing or residual-cap condition is assumed: both follow
from the locally initialized recurrence at the logarithmic analysis time. -/
theorem domination_bound (p : NeighborhoodSlack.Parameters)
    (hden : Incidence.InducedDensityBound G p.a) {m : ℕ} (hm : 0 < m)
    (hrho : 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) :
    let S := selected G (CappedGrowth.rho m) (state G p m (CappedGrowth.timeBound m Delta))
    dominates G (CappedSelection.output G S) ∧
      ((CappedSelection.output G S).card : ℝ) ≤ (2*p.a+1)*fractionalNumber G := by
  let y := state G p m (CappedGrowth.timeBound m Delta)
  have hh := state_invariant G p hm (CappedGrowth.timeBound m Delta)
  apply CappedSelection.terminal_fractionalNumber G p hden _ y (CappedGrowth.rho m)
    hh.1 hh.2.1 hh.2.2 hrho
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro v hv
    have hn := (Finset.mem_sdiff.mp hv).2
    exact (terminal G p hm Delta hdegree v).resolve_left
      (fun hb => hn ((blocked_iff_covered G _ _ _).mp hb))

theorem local_certificate (p : NeighborhoodSlack.Parameters) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    CappedLocalHalt.certificate G (cap p) (CappedGrowth.rho m)
      (state G p m (CappedGrowth.timeBound m Delta)) v := by
  intro r _ u _
  exact terminal G p hm Delta hdegree u

end Paper.Density.CappedConvergence
#print axioms Paper.Density.CappedConvergence.parameters
#print axioms Paper.Density.CappedConvergence.domination_bound
#print axioms Paper.Density.CappedConvergence.local_certificate
