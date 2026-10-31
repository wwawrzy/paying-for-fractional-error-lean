import Paper.Solver.Density.UnitDomination

/-! Capped multiplicative packing updates. Each update uses only a vertex's
value and the tightness bits of its closed neighbors. No maximum degree or
global stopping horizon is an input to the transition. -/
namespace Paper.Density.CappedDynamics
open SevenFoundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def blocked (rho : ℝ) (y : V → ℝ) (v : V) : Prop :=
  ∃ r ∈ closed G v, rho ≤ UnitDomination.mass G y r

noncomputable def step (cap factor rho : ℝ) (y : V → ℝ) (v : V) : ℝ :=
  if blocked G rho y v then y v else min cap (factor * y v)

noncomputable def run (cap factor rho : ℝ) (initial : V → ℝ) : ℕ → V → ℝ
  | 0 => initial
  | n + 1 => step G cap factor rho (run cap factor rho initial n)

theorem blocked_mono {rho : ℝ} {y z : V → ℝ} (h : ∀ v, y v ≤ z v)
    {v : V} (hv : blocked G rho y v) : blocked G rho z v := by
  obtain ⟨r, hr, hm⟩ := hv
  exact ⟨r, hr, hm.trans (Finset.sum_le_sum (fun u _ => h u))⟩

theorem step_bounds {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (y : V → ℝ) (hy : ∀ v, 0 ≤ y v) (hcap : ∀ v, y v ≤ cap) (v : V) :
    y v ≤ step G cap factor rho y v ∧ step G cap factor rho y v ≤ cap ∧
      step G cap factor rho y v ≤ factor * y v := by
  have hg : y v ≤ factor * y v := by nlinarith [hy v]
  unfold step
  split_ifs
  · exact ⟨le_rfl, hcap v, hg⟩
  · exact ⟨le_min (hcap v) hg, min_le_left _ _, min_le_right _ _⟩

theorem step_packing {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (y : V → ℝ)
    (hy : ∀ v, 0 ≤ y v) (hcap : ∀ v, y v ≤ cap)
    (hpack : ∀ r, UnitDomination.mass G y r ≤ 1) :
    ∀ r, UnitDomination.mass G (step G cap factor rho y) r ≤ 1 := by
  intro r
  by_cases ht : rho ≤ UnitDomination.mass G y r
  · have he : UnitDomination.mass G (step G cap factor rho y) r =
        UnitDomination.mass G y r := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_pos ⟨r, (closed_symm G v r).mp hv, ht⟩
    rw [he]
    exact hpack r
  · calc
      _ ≤ ∑ v ∈ closed G r, factor * y v :=
        Finset.sum_le_sum (fun v _ => (step_bounds G hc hf y hy hcap v).2.2)
      _ = factor * UnitDomination.mass G y r := (Finset.mul_sum ..).symm
      _ ≤ factor * rho := mul_le_mul_of_nonneg_left (le_of_not_ge ht) (by linarith)
      _ ≤ 1 := hr

theorem run_invariant {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (initial : V → ℝ)
    (hi : ∀ v, 0 ≤ initial v) (hic : ∀ v, initial v ≤ cap)
    (hip : ∀ r, UnitDomination.mass G initial r ≤ 1) (n : ℕ) :
    (∀ v, 0 ≤ run G cap factor rho initial n v) ∧
    (∀ v, run G cap factor rho initial n v ≤ cap) ∧
    (∀ r, UnitDomination.mass G (run G cap factor rho initial n) r ≤ 1) := by
  induction n with
  | zero => exact ⟨hi, hic, hip⟩
  | succ n ih =>
    refine ⟨?_, ?_, step_packing G hc hf hr _ ih.1 ih.2.1 ih.2.2⟩
    · intro v
      exact (ih.1 v).trans (step_bounds G hc hf _ ih.1 ih.2.1 v).1
    · intro v
      exact (step_bounds G hc hf _ ih.1 ih.2.1 v).2.1

theorem run_mono {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (initial : V → ℝ)
    (hi : ∀ v, 0 ≤ initial v) (hic : ∀ v, initial v ≤ cap)
    (hip : ∀ r, UnitDomination.mass G initial r ≤ 1) (v : V) :
    Monotone (fun n => run G cap factor rho initial n v) := by
  apply monotone_nat_of_le_succ
  intro n
  have hh := run_invariant G hc hf hr initial hi hic hip n
  exact (step_bounds G hc hf _ hh.1 hh.2.1 v).1

/-- An unfrozen value below the cap has undergone every multiplicative update.
This supplies the progress argument, not an assumed terminal certificate. -/
theorem unblocked_growth {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (initial : V → ℝ)
    (hi : ∀ v, 0 ≤ initial v) (hic : ∀ v, initial v ≤ cap)
    (hip : ∀ r, UnitDomination.mass G initial r ≤ 1) (n : ℕ) (v : V)
    (hb : ¬ blocked G rho (run G cap factor rho initial n) v)
    (hlt : run G cap factor rho initial n v < cap) :
    factor ^ n * initial v ≤ run G cap factor rho initial n v := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : ∀ u, run G cap factor rho initial n u ≤ run G cap factor rho initial (n+1) u :=
      fun u => run_mono G hc hf hr initial hi hic hip u (Nat.le_succ n)
    have hb' : ¬ blocked G rho (run G cap factor rho initial n) v :=
      fun h => hb (blocked_mono G hm h)
    have hg := ih hb' ((hm v).trans_lt hlt)
    have he : run G cap factor rho initial (n+1) v =
        min cap (factor * run G cap factor rho initial n v) := if_neg hb'
    rw [he] at hlt ⊢
    have hsmall : factor * run G cap factor rho initial n v < cap := by
      by_contra h
      rw [min_eq_left (le_of_not_gt h)] at hlt
      exact (lt_irrefl cap) hlt
    rw [min_eq_right hsmall.le, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ factor by linarith)]

/-- A bound on growth is used only in the analysis, never by the transition. -/
theorem terminal_of_growth {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (initial : V → ℝ)
    (hi : ∀ v, 0 ≤ initial v) (hic : ∀ v, initial v ≤ cap)
    (hip : ∀ r, UnitDomination.mass G initial r ≤ 1) (n : ℕ)
    (hreach : ∀ v, cap ≤ factor ^ n * initial v) (v : V) :
    blocked G rho (run G cap factor rho initial n) v ∨
      run G cap factor rho initial n v = cap := by
  by_cases hb : blocked G rho (run G cap factor rho initial n) v
  · exact Or.inl hb
  · right
    have hcap := (run_invariant G hc hf hr initial hi hic hip n).2.1 v
    by_contra hne
    have hlt := lt_of_le_of_ne hcap hne
    have hg := unblocked_growth G hc hf hr initial hi hic hip n v hb hlt
    exact (not_lt_of_ge ((hreach v).trans hg)) hlt

theorem terminal_fixed {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (y : V → ℝ) (hterminal : ∀ v, blocked G rho y v ∨ y v = cap) :
    step G cap factor rho y = y := by
  funext v
  unfold step
  split_ifs with h
  · rfl
  · have he := (hterminal v).resolve_left h
    rw [he, min_eq_left]
    nlinarith

end Paper.Density.CappedDynamics
#print axioms Paper.Density.CappedDynamics.step_packing
#print axioms Paper.Density.CappedDynamics.run_invariant
#print axioms Paper.Density.CappedDynamics.unblocked_growth
#print axioms Paper.Density.CappedDynamics.terminal_of_growth
#print axioms Paper.Density.CappedDynamics.terminal_fixed
