import Paper.Solver.Density.CappedDynamics

/-! A local certificate for irrevocable output in capped dual growth. The
certificate examines frozen bits within two hops; it contains no global clock
or degree parameter. Reaching it follows from the growth bound. -/
namespace Paper.Density.CappedLocalHalt
open SevenFoundation CappedDynamics
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def finished (cap rho : ℝ) (y : V → ℝ) (v : V) : Prop :=
  blocked G rho y v ∨ y v = cap

def certificate (cap rho : ℝ) (y : V → ℝ) (v : V) : Prop :=
  ∀ r ∈ closed G v, ∀ u ∈ closed G r, finished G cap rho y u

noncomputable def outputBit (rho : ℝ) (y : V → ℝ) (v : V) : Bool :=
  decide (rho ≤ UnitDomination.mass G y v ∨ ¬ blocked G rho y v)

variable {cap factor rho : ℝ} (hc : 0 ≤ cap) (hf : 1 ≤ factor)
    (hr : factor * rho ≤ 1) (initial : V → ℝ)
    (hi : ∀ v, 0 ≤ initial v) (hic : ∀ v, initial v ≤ cap)
    (hip : ∀ r, UnitDomination.mass G initial r ≤ 1)
include hc hf hr hi hic hip

theorem finished_persistent {n m : ℕ} (hnm : n ≤ m) (v : V)
    (h : finished G cap rho (run G cap factor rho initial n) v) :
    finished G cap rho (run G cap factor rho initial m) v := by
  rcases h with h | h
  · left
    exact blocked_mono G (fun u => run_mono G hc hf hr initial hi hic hip u hnm) h
  · right
    apply le_antisymm ((run_invariant G hc hf hr initial hi hic hip m).2.1 v)
    exact h.symm.trans_le (run_mono G hc hf hr initial hi hic hip v hnm)

theorem finished_value (n k : ℕ) (v : V)
    (h : finished G cap rho (run G cap factor rho initial n) v) :
    run G cap factor rho initial (n+k) v = run G cap factor rho initial n v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := finished_persistent G hc hf hr initial hi hic hip (Nat.le_add_right n k) v h
    have he : step G cap factor rho (run G cap factor rho initial (n+k)) v =
        run G cap factor rho initial (n+k) v := by
      unfold step
      split_ifs with hb
      · rfl
      · have heq := hh.resolve_left hb
        rw [heq, min_eq_left]
        nlinarith
    change step G cap factor rho (run G cap factor rho initial (n+k)) v = _
    exact he.trans ih

/-- The two-hop frozen certificate fixes every tightness bit on the closed
neighborhood, hence both clauses of the actual output decision. -/
theorem certified_output_stable (n k : ℕ) (v : V)
    (h : certificate G cap rho (run G cap factor rho initial n) v) :
    outputBit G rho (run G cap factor rho initial (n+k)) v =
      outputBit G rho (run G cap factor rho initial n) v := by
  have hm : ∀ r ∈ closed G v,
      UnitDomination.mass G (run G cap factor rho initial (n+k)) r =
      UnitDomination.mass G (run G cap factor rho initial n) r := by
    intro r hr'
    apply Finset.sum_congr rfl
    intro u hu
    exact finished_value G hc hf hr initial hi hic hip n k u (h r hr' u hu)
  have hb : blocked G rho (run G cap factor rho initial (n+k)) v ↔
      blocked G rho (run G cap factor rho initial n) v := by
    constructor <;> rintro ⟨r, hr', ht⟩
    · exact ⟨r, hr', by simpa only [hm r hr'] using ht⟩
    · exact ⟨r, hr', by simpa only [hm r hr'] using ht⟩
  simp only [outputBit, hm v (self_mem_closed G v), hb]

theorem certificate_of_growth (n : ℕ)
    (hreach : ∀ v, cap ≤ factor ^ n * initial v) (v : V) :
    certificate G cap rho (run G cap factor rho initial n) v := by
  intro r _ u _
  exact terminal_of_growth G hc hf hr initial hi hic hip n hreach u

end Paper.Density.CappedLocalHalt
#print axioms Paper.Density.CappedLocalHalt.finished_value
#print axioms Paper.Density.CappedLocalHalt.certified_output_stable
#print axioms Paper.Density.CappedLocalHalt.certificate_of_growth
