import Paper.Communication.CachedProgramResources
import Paper.Solver.Density.CappedSilentExecution

/-! Actual optional transmissions and message widths of the repeated silent
execution. A phase still consists of six consecutive rounds. Omitted messages
cost zero bits, and active senders use the original finite-string encodings. -/
namespace Paper.Density.CappedSilentResources

open PrefixBroadcast.Program

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The runtime transmission in one slot of one six-round phase. -/
def phaseWire (cap : ℚ) (m : ℕ) (rho : ℚ) (n i : ℕ) (v : V) : Option (List Bool) :=
  let s := CappedSilentExecution.run G cap m rho n
  (CappedOutputRegister.phase cap m rho).cachedSent G s.quiet s.values s.memory 0 i v

/-- The execution invariant supplies exactly the generic cache-readiness premise. -/
theorem ready (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n : ℕ) :
    ∀ i < (CappedOutputRegister.phase (V := V) cap m rho).rounds, ∀ v u,
      (v = u ∨ G.Adj v u) → (CappedSilentExecution.run G cap m rho n).quiet u = true →
      (CappedSilentExecution.run G cap m rho n).memory v u (0+i) =
        (CappedOutputRegister.phase cap m rho).sent G
          (CappedSilentExecution.run G cap m rho n).values i u := by
  have h := CappedSilentExecution.run_refines G cap hm hcap rho hrho n
  intro i hi v u ha hq
  have hi6 : i < 6 := by simpa only [CappedOutputRegister.phase_rounds] using hi
  have hqu : CappedReplay.quiet G cap m rho u n = true := by
    simpa only [h.2.1] using hq
  rw [Nat.zero_add, h.2.2 v u i ha hi6,
    CappedReplay.silent_ready G cap hm hcap rho hrho u n hqu]
  change ((CappedReplay.trace G cap m rho u n)[i]?).getD [] = _
  rw [h.1, CappedPhaseTrace.phase_sent G cap m rho _ i u hi6]
  rfl

/-- Each active runtime transmission is precisely the corresponding reference word. -/
theorem phaseWire_eq (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1)
    (n i : ℕ) (v : V) (hi : i < 6) :
    phaseWire G cap m rho n i v =
      if CappedReplay.quiet G cap m rho v n then none else
        some ((CappedOutputRegister.phase cap m rho).sent G
          (CappedSilentExecution.reference G cap m rho n) i v) := by
  unfold phaseWire
  rw [cachedSent_correct G _ _ _ _ 0 i v
      (by simpa only [CappedOutputRegister.phase_rounds] using hi)
      (ready G cap hm hcap rho hrho n),
    CappedSilentExecution.run_quiet G cap hm hcap rho hrho n,
    CappedSilentExecution.run_values G cap hm hcap rho hrho n]

/-- Replay preserves the original per-round finite-string width bound. -/
theorem phaseWire_bits (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1)
    (n i : ℕ) (v : V) (hi : i < 6) (Delta extra : ℕ)
    (hdegree : ∀ u, G.degree u ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta + extra) :
    sentBits (phaseWire G cap m rho n i v) ≤
      (2*m + 2*extra + 5) * Nat.clog 2 (Fintype.card V + 2) := by
  have hb := cachedSent_bits_le G (CappedSilentExecution.run G cap m rho n).quiet
    (CappedOutputRegister.phase cap m rho) (CappedSilentExecution.run G cap m rho n).values
    (CappedSilentExecution.run G cap m rho n).memory 0 i v
    (by simpa only [CappedOutputRegister.phase_rounds] using hi)
    (ready G cap hm hcap rho hrho n)
  refine hb.trans ?_
  rw [CappedSilentExecution.run_values G cap hm hcap rho hrho n,
    CappedOutputRegister.phase_bits_eq]
  exact CappedProtocolSchedules.phase_bits G cap m rho n Delta extra hdegree hD hn

/-- A quiet runtime sender transmits nothing, including outside the valid slots. -/
theorem phaseWire_none_of_quiet (cap : ℚ) (m : ℕ) (rho : ℚ) (n i : ℕ) (v : V)
    (hq : (CappedSilentExecution.run G cap m rho n).quiet v = true) :
    phaseWire G cap m rho n i v = none :=
  cachedSent_quiet G _ _ _ _ _ i v hq

/-- At public parameters every sender is silent after the notifying phase.
The degree bound and time bound occur only in this analysis statement. -/
theorem phaseWire_none_after_bound (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (Delta : ℕ) (hdegree : ∀ u, G.degree u ≤ Delta) (k i : ℕ) (v : V) :
    phaseWire G cap m (CappedUniformParameters.rho m)
      (CappedGrowth.timeBound m Delta + 1 + k) i v = none := by
  have hcapR : (0 : ℝ) ≤ (cap : ℝ) := hc.symm ▸ (CappedConvergence.cap_bounds p).1.le
  have hcap : 0 ≤ cap := by exact_mod_cast hcapR
  have hrhoR : (CappedCounterState.scale m : ℝ) * (CappedUniformParameters.rho m : ℝ) ≤ 1 := by
    rw [CappedUniformParameters.scale_cast, CappedUniformParameters.rho_cast]
    exact (CappedGrowth.factor_mul_rho hm).le
  have hrho : CappedCounterState.scale m * CappedUniformParameters.rho m ≤ 1 := by
    exact_mod_cast hrhoR
  apply phaseWire_none_of_quiet
  rw [CappedSilentExecution.run_quiet G cap hm hcap _ hrho]
  exact CappedReplay.quiet_after_bound G p cap hc hm Delta hdegree v k

end Paper.Density.CappedSilentResources

#print axioms Paper.Density.CappedSilentResources.ready
#print axioms Paper.Density.CappedSilentResources.phaseWire_eq
#print axioms Paper.Density.CappedSilentResources.phaseWire_bits
#print axioms Paper.Density.CappedSilentResources.phaseWire_none_of_quiet
#print axioms Paper.Density.CappedSilentResources.phaseWire_none_after_bound
