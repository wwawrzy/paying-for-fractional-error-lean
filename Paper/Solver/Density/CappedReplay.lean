import Paper.Communication.PeriodicReplay
import Paper.Solver.Density.CappedFrozenMessages
import Paper.Solver.Density.CappedCompletion

/-!
Local replay of the capped execution's six consecutive encoded broadcasts.
Each frame is an analysis grouping of six rounds, not a single-round message.
The cache and silence transitions depend only on the local near notification.
The graph-dependent trace extracts messages from the ordinary execution for the
refinement proof. It is not an implementation of a silent network execution.
-/
namespace Paper.Density.CappedReplay

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The six actual encoded messages in one ordinary execution phase. -/
def trace (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) (n : ℕ) : List (List Bool) :=
  CappedFrozenMessages.phaseMessages G cap m rho (CappedExecution.run G cap m rho n) v

/-- The local notification announces that the phase template is permanent. -/
def notify (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) (n : ℕ) : Bool :=
  (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho n) v).near

def quiet (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) : ℕ → Bool :=
  PeriodicReplay.quiet (notify G cap m rho v)

def wire (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) : ℕ → Option (List (List Bool)) :=
  PeriodicReplay.wire (trace G cap m rho v) (notify G cap m rho v)

/-- The receiver starts empty and retains the last complete received frame. -/
def cache (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) : ℕ → List (List Bool) :=
  PeriodicReplay.cache (trace G cap m rho v) (notify G cap m rho v) []

theorem stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (v : V) :
    PeriodicReplay.StableAfterNotification (trace G cap m rho v) (notify G cap m rho v) := by
  intro n hn k
  exact CappedFrozenMessages.phaseMessages_stable G cap hm hcap rho hrho n k v hn

/-- The full six-round frame can be recovered exactly after every phase. -/
theorem cache_succ_eq_trace (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (v : V) (n : ℕ) :
    cache G cap m rho v (n + 1) = trace G cap m rho v n :=
  PeriodicReplay.cache_succ_eq_trace _ _ [] (stable G cap hm hcap rho hrho v) n

/-- At the start of a quiet phase its ordinary frame is already cached. -/
theorem silent_ready (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (v : V) (n : ℕ)
    (hq : quiet G cap m rho v n = true) :
    cache G cap m rho v n = trace G cap m rho v n := by
  simpa only [Nat.add_zero] using
    PeriodicReplay.quiet_cache_future _ _ [] (stable G cap hm hcap rho hrho v) n 0 hq

theorem silent_wire_none (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) (n : ℕ)
    (hq : quiet G cap m rho v n = true) : wire G cap m rho v n = none :=
  PeriodicReplay.quiet_wire_none _ _ n hq

theorem notify_quiet (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) (n k : ℕ)
    (hn : notify G cap m rho v n = true) : quiet G cap m rho v (n + 1 + k) = true :=
  PeriodicReplay.notify_quiet _ n hn k

/-- Each of the six message slots is preserved, including its bit-string contents. -/
theorem cache_slot_eq (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (v : V) (n slot : ℕ) :
    (cache G cap m rho v (n + 1))[slot]? = (trace G cap m rho v n)[slot]? := by
  rw [cache_succ_eq_trace G cap hm hcap rho hrho]

/-- The degree bound is used only to bound notification time in the analysis. -/
theorem notify_at_bound (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    notify G cap m (CappedUniformParameters.rho m) v (CappedGrowth.timeBound m Delta) = true := by
  apply (CappedHaltRounds.near_iff G cap m (CappedUniformParameters.rho m) _ v).mpr
  rw [CappedCompletion.decoded_state G p cap hc hm, hc, CappedUniformParameters.rho_cast]
  intro u _
  exact CappedConvergence.terminal G p hm Delta hdegree u

/-- Silence begins after the notifying phase and persists thereafter. -/
theorem quiet_after_bound (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) (k : ℕ) :
    quiet G cap m (CappedUniformParameters.rho m) v
      (CappedGrowth.timeBound m Delta + 1 + k) = true :=
  notify_quiet G cap m _ v _ k (notify_at_bound G p cap hc hm Delta hdegree v)

end Paper.Density.CappedReplay

#print axioms Paper.Density.CappedReplay.stable
#print axioms Paper.Density.CappedReplay.cache_succ_eq_trace
#print axioms Paper.Density.CappedReplay.silent_ready
#print axioms Paper.Density.CappedReplay.cache_slot_eq
#print axioms Paper.Density.CappedReplay.notify_at_bound
#print axioms Paper.Density.CappedReplay.quiet_after_bound
