import Paper.Solver.Density.CappedPhaseTrace
import Paper.Solver.Density.CappedReplay

/-! Actual repeated execution with receiver caches and silent senders.
After a complete six-round phase, each vertex reads its own recorded fourth
message to decide whether all its future sends may be suppressed. The
runtime never reads the reference trace, a global degree, or a time bound. -/
namespace Paper.Density.CappedSilentExecution
open CappedCounterState (State)

structure NetworkState (V : Type) where
  values : V → State × Option Bool
  memory : PrefixBroadcast.Program.Cache V
  quiet : V → Bool

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def initial (cap : ℚ) : NetworkState V :=
  ⟨(CappedOutputRegister.startup cap).run G (fun _ => PUnit.unit),
    fun _ _ _ => [], fun _ => false⟩

/-- The notifying phase is sent in full. Later phases use silence and the
receiver's own cache; reading the local fourth-slot record adds no round. -/
def step (cap : ℚ) (m : ℕ) (rho : ℚ) (s : NetworkState V) : NetworkState V :=
  let next := (CappedOutputRegister.phase cap m rho).cachedRun G s.quiet s.values s.memory 0
  ⟨next.1, next.2, fun v => s.quiet v || decide (next.2 v v 3 = [true])⟩

def run (cap : ℚ) (m : ℕ) (rho : ℚ) : ℕ → NetworkState V
  | 0 => initial G cap
  | n+1 => step G cap m rho (run cap m rho n)

/-- The reference state is used only in correctness proofs. -/
def reference (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) : V → State × Option Bool :=
  fun v => (CappedExecution.run G cap m rho n v, CappedOutputRegister.before G cap m rho n v)

theorem trace_notification (cap : ℚ) (m : ℕ) (rho : ℚ) (v : V) (n : ℕ) :
    ((CappedReplay.trace G cap m rho v n)[3]?).getD [] =
      [CappedReplay.notify G cap m rho v n] := by
  unfold CappedReplay.trace
  rw [CappedFrozenMessages.phaseMessages_eq]
  rfl

theorem run_refines (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n : ℕ) :
    (run G cap m rho n).values = reference G cap m rho n ∧
      (run G cap m rho n).quiet = (fun v => CappedReplay.quiet G cap m rho v n) ∧
      (∀ v u i, (v = u ∨ G.Adj v u) → i < 6 →
        (run G cap m rho n).memory v u i =
          ((CappedReplay.cache G cap m rho u n)[i]?).getD []) := by
  induction n with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro v u i _ _
    rfl
  | succ n ih =>
    let s := run G cap m rho n
    let P := CappedOutputRegister.phase (V := V) cap m rho
    have hready : ∀ i < P.rounds, ∀ v u, (v = u ∨ G.Adj v u) → s.quiet u = true →
        s.memory v u (0+i) = P.sent G s.values i u := by
      intro i hi v u ha hq
      have hi6 : i < 6 := by simpa only [P, CappedOutputRegister.phase_rounds] using hi
      have hqu : CappedReplay.quiet G cap m rho u n = true := by
        simpa only [s, ih.2.1] using hq
      change (run G cap m rho n).memory v u (0+i) = _
      rw [Nat.zero_add, ih.2.2 v u i ha hi6,
        CappedReplay.silent_ready G cap hm hcap rho hrho u n hqu]
      change ((CappedReplay.trace G cap m rho u n)[i]?).getD [] =
        (CappedOutputRegister.phase cap m rho).sent G (run G cap m rho n).values i u
      rw [ih.1, CappedPhaseTrace.phase_sent G cap m rho _ i u hi6]
      rfl
    have hc := PrefixBroadcast.Program.cachedRun_correct G s.quiet P s.values s.memory 0 hready
    have hmemory : ∀ v u i, (v = u ∨ G.Adj v u) → i < 6 →
        (P.cachedRun G s.quiet s.values s.memory 0).2 v u i =
          ((CappedReplay.cache G cap m rho u (n+1))[i]?).getD [] := by
      intro v u i ha hi
      have hh := hc.2.1 v u i ha (by simpa only [P, CappedOutputRegister.phase_rounds] using hi)
      simp only [Nat.zero_add] at hh
      rw [CappedReplay.cache_succ_eq_trace G cap hm hcap rho hrho u n]
      rw [hh]
      change (CappedOutputRegister.phase cap m rho).sent G (run G cap m rho n).values i u = _
      rw [ih.1, CappedPhaseTrace.phase_sent G cap m rho _ i u hi]
      rfl
    refine ⟨?_, ?_, hmemory⟩
    · change (P.cachedRun G s.quiet s.values s.memory 0).1 = _
      rw [hc.1]
      change (CappedOutputRegister.phase cap m rho).run G (run G cap m rho n).values = _
      rw [ih.1, CappedOutputRegister.phase_run]
      rfl
    · funext v
      change (s.quiet v || decide ((P.cachedRun G s.quiet s.values s.memory 0).2 v v 3 = [true])) = _
      rw [hmemory v v 3 (Or.inl rfl) (by decide),
        CappedReplay.cache_succ_eq_trace G cap hm hcap rho hrho v n, trace_notification]
      change ((run G cap m rho n).quiet v || decide ([CappedReplay.notify G cap m rho v n] = [true])) = _
      rw [ih.2.1]
      change (CappedReplay.quiet G cap m rho v n || decide ([CappedReplay.notify G cap m rho v n] = [true])) =
        (CappedReplay.quiet G cap m rho v n || CappedReplay.notify G cap m rho v n)
      cases CappedReplay.notify G cap m rho v n <;> simp

theorem run_values (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n : ℕ) :
    (run G cap m rho n).values = reference G cap m rho n :=
  (run_refines G cap hm hcap rho hrho n).1

theorem run_quiet (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n : ℕ) :
    (run G cap m rho n).quiet = (fun v => CappedReplay.quiet G cap m rho v n) :=
  (run_refines G cap hm hcap rho hrho n).2.1

end Paper.Density.CappedSilentExecution
#print axioms Paper.Density.CappedSilentExecution.run_refines
