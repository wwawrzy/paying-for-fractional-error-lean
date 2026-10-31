import Paper.Solver.Density.CappedRegisteredCompletion
import Paper.Solver.Density.CappedReplay
import Paper.Solver.Density.CappedFrozenPackets

/-! Reference-state absorption after a local output register is populated.
The register's actual history supplies an earlier successful certificate;
no finished-state or neighbor-silence conclusion is assumed. This supports
a later per-vertex halt wrapper without changing the silent runtime here. -/

namespace Paper.Density.CappedLocalAbsorption

open SevenFoundation
open CappedOutputRegister (before latch)
open CappedCompletion (firstTime)
open CappedUniformParameters (rho)

private theorem cap_nonneg (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) : 0 ≤ cap := by
  have h : (0 : ℝ) ≤ (cap : ℝ) := hc.symm ▸ (CappedConvergence.cap_bounds p).1.le
  exact_mod_cast h

private theorem scale_rho_le {m : ℕ} (hm : 0 < m) :
    CappedCounterState.scale m * rho m ≤ 1 := by
  have h : (CappedCounterState.scale m : ℝ) * (rho m : ℝ) ≤ 1 := by
    rw [CappedUniformParameters.scale_cast, CappedUniformParameters.rho_cast]
    exact (CappedGrowth.factor_mul_rho hm).le
  exact_mod_cast h

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual private latch is absorbing independently of future probes. -/
theorem register_stable (cap : ℚ) (m : ℕ) (threshold : ℚ) (n k : ℕ) (v : V)
    (b : Bool) (hb : before G cap m threshold n v = some b) :
    before G cap m threshold (n + k) v = before G cap m threshold n v := by
  induction k with
  | zero => simp
  | succ k ih =>
    change latch (before G cap m threshold (n + k) v) _ = _
    rw [ih, hb]
    rfl

theorem firstTime_lt (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n : ℕ) (v : V) (b : Bool) (hb : before G cap m (rho m) n v = some b) :
    firstTime G p cap hc hm v < n := by
  by_contra h
  have hn : n ≤ firstTime G p cap hc hm v := le_of_not_gt h
  have he := CappedRegisteredCompletion.before_none G p cap hc hm v n hn
  rw [hb] at he
  cases he

theorem first_certificate (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m) (v : V) :
    CappedLocalHalt.certificate G (cap : ℝ) (rho m : ℝ)
      (fun u => (CappedCounterState.decode cap m
        (CappedExecution.run G cap m (rho m) (firstTime G p cap hc hm v) u) : ℝ)) v := by
  exact (CappedHaltRounds.probe_done_iff G cap m (rho m) _ v).mp
    (CappedCompletion.firstTime_done G p cap hc hm v)

/-- A populated register implies that the compact state is already fixed. -/
theorem state_stable (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n k : ℕ) (v : V) (b : Bool) (hb : before G cap m (rho m) n v = some b) :
    CappedExecution.run G cap m (rho m) (n + k) v = CappedExecution.run G cap m (rho m) n v := by
  have ht := firstTime_lt G p cap hc hm n v b hb
  have hcert := first_certificate G p cap hc hm v
  have hf := hcert v (self_mem_closed G v) v (self_mem_closed G v)
  have hn := CappedFrozenPackets.finished_persistent G cap hm (cap_nonneg p cap hc)
    (rho m) (scale_rho_le hm) (Nat.le_of_lt ht) v hf
  exact CappedFrozenPackets.state_stable G cap hm (cap_nonneg p cap hc)
    (rho m) (scale_rho_le hm) n k v hn

/-- The first successful certificate already notified every closed neighbor;
the before-register is populated only after that notifying phase finishes. -/
theorem neighbors_quiet (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n : ℕ) (v : V) (b : Bool) (hb : before G cap m (rho m) n v = some b) :
    ∀ u ∈ closed G v, CappedReplay.quiet G cap m (rho m) u n = true := by
  let t := firstTime G p cap hc hm v
  have ht : t < n := firstTime_lt G p cap hc hm n v b hb
  have hcert := first_certificate G p cap hc hm v
  intro u hu
  have hnotify : CappedReplay.notify G cap m (rho m) u t = true :=
    (CappedHaltRounds.near_iff G cap m (rho m) _ u).mpr (hcert u hu)
  have hq := CappedReplay.notify_quiet G cap m (rho m) u t (n - (t + 1)) hnotify
  have he : t + 1 + (n - (t + 1)) = n := Nat.add_sub_of_le (by omega)
  rwa [he] at hq

/-- Every closed neighbor is silent and its cached six-message frame is
constant, so later input frames carry no new local information. -/
theorem neighbors_cache_stable (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n k : ℕ) (v : V) (b : Bool) (hb : before G cap m (rho m) n v = some b) :
    ∀ u ∈ closed G v, CappedReplay.quiet G cap m (rho m) u n = true ∧
      CappedReplay.cache G cap m (rho m) u (n + k) = CappedReplay.cache G cap m (rho m) u n := by
  intro u hu
  have hq := neighbors_quiet G p cap hc hm n v b hb u hu
  have hqfuture : CappedReplay.quiet G cap m (rho m) u (n + k) = true :=
    PeriodicReplay.quiet_add (CappedReplay.notify G cap m (rho m) u) n hq k
  have hfuture := CappedReplay.silent_ready G cap hm (cap_nonneg p cap hc)
    (rho m) (scale_rho_le hm) u (n + k) hqfuture
  have hearlier : CappedReplay.cache G cap m (rho m) u n =
      CappedReplay.trace G cap m (rho m) u (n + k) :=
    PeriodicReplay.quiet_cache_future (CappedReplay.trace G cap m (rho m) u)
      (CappedReplay.notify G cap m (rho m) u) []
      (CappedReplay.stable G cap hm (cap_nonneg p cap hc) (rho m) (scale_rho_le hm) u) n k hq
  exact ⟨hq, hfuture.trans hearlier.symm⟩

/-- Reference local state, output register, and all closed-neighbor frame
caches are absorbed once the actual output register contains a bit. -/
theorem absorbed (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n k : ℕ) (v : V) (b : Bool) (hb : before G cap m (rho m) n v = some b) :
    CappedExecution.run G cap m (rho m) (n + k) v = CappedExecution.run G cap m (rho m) n v ∧
      before G cap m (rho m) (n + k) v = before G cap m (rho m) n v ∧
      ∀ u ∈ closed G v, CappedReplay.quiet G cap m (rho m) u n = true ∧
        CappedReplay.cache G cap m (rho m) u (n + k) = CappedReplay.cache G cap m (rho m) u n :=
  ⟨state_stable G p cap hc hm n k v b hb,
    register_stable G cap m (rho m) n k v b hb,
    neighbors_cache_stable G p cap hc hm n k v b hb⟩

end Paper.Density.CappedLocalAbsorption

#print axioms Paper.Density.CappedLocalAbsorption.firstTime_lt
#print axioms Paper.Density.CappedLocalAbsorption.state_stable
#print axioms Paper.Density.CappedLocalAbsorption.neighbors_quiet
#print axioms Paper.Density.CappedLocalAbsorption.neighbors_cache_stable
#print axioms Paper.Density.CappedLocalAbsorption.absorbed
