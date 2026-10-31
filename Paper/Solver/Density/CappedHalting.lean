import Paper.Solver.Density.CappedLocalAbsorption
import Paper.Solver.Density.CappedSilentMemory
import Paper.Solver.Density.CappedSilentParameters

/-! A local halt transition retaining completed vertices' entire local state.
The private output register alone triggers halting. No deadline or degree is
an input to the transition. Quiet senders emit no physical messages in the
cached phase; completed receivers retain their old memory as well as values. -/
namespace Paper.Density.CappedHalting
open SevenFoundation
open CappedSilentExecution (NetworkState)
open CappedUniformParameters (rho)

variable {V : Type}

private theorem network_ext (s t : NetworkState V)
    (hv : s.values = t.values) (hmem : s.memory = t.memory) (hq : s.quiet = t.quiet) :
    s = t := by
  cases s
  cases t
  cases hv
  cases hmem
  cases hq
  rfl

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Phase-entry suppression is determined independently at each vertex. -/
def entryQuiet (s : NetworkState V) : V → Bool :=
  fun v => s.quiet v || (s.values v).2.isSome

/-- Active vertices execute the cached phase. Completed vertices keep their
entire values and receiver memory, and remain quiet. The phase uses the
entry quiet flags, so a completed vertex sends no physical message. -/
def haltedStep (cap : ℚ) (m : ℕ) (threshold : ℚ) (s : NetworkState V) : NetworkState V :=
  let next := CappedSilentExecution.step G cap m threshold
    { s with quiet := entryQuiet s }
  ⟨fun v => if (s.values v).2.isSome then s.values v else next.values v,
    fun v => if (s.values v).2.isSome then s.memory v else next.memory v,
    fun v => if (s.values v).2.isSome then true else next.quiet v⟩

def haltedRun (cap : ℚ) (m : ℕ) (threshold : ℚ) : ℕ → NetworkState V
  | 0 => CappedSilentExecution.initial G cap
  | n+1 => haltedStep G cap m threshold (haltedRun cap m threshold n)

/-- Retention is part of the transition itself, for arbitrary inputs. -/
theorem haltedStep_completed (cap : ℚ) (m : ℕ) (threshold : ℚ)
    (s : NetworkState V) (v : V) (b : Bool) (hb : (s.values v).2 = some b) :
    (haltedStep G cap m threshold s).values v = s.values v ∧
    (haltedStep G cap m threshold s).memory v = s.memory v ∧
    (haltedStep G cap m threshold s).quiet v = true ∧ entryQuiet s v = true := by
  simp [haltedStep, entryQuiet, hb]

private theorem cap_nonneg (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) : 0 ≤ cap := by
  have h : (0 : ℝ) ≤ (cap : ℝ) := hc.symm ▸ (CappedConvergence.cap_bounds p).1.le
  exact_mod_cast h

/-- A populated runtime register implies full local absorption, including
every sender and every slot of the receiver memory. -/
theorem completed_stable (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n k : ℕ) (v : V) (b : Bool)
    (hb : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 = some b) :
    (CappedSilentExecution.run G cap m (rho m) n).quiet v = true ∧
    (CappedSilentExecution.run G cap m (rho m) (n+k)).values v =
      (CappedSilentExecution.run G cap m (rho m) n).values v ∧
    (CappedSilentExecution.run G cap m (rho m) (n+k)).memory v =
      (CappedSilentExecution.run G cap m (rho m) n).memory v ∧
    (CappedSilentExecution.run G cap m (rho m) (n+k)).quiet v = true := by
  have hcap := cap_nonneg p cap hc
  have hs := (CappedSilentParameters.scale_mul_rho hm).le
  have hn := CappedSilentExecution.run_refines G cap hm hcap (rho m) hs n
  have hnk := CappedSilentExecution.run_refines G cap hm hcap (rho m) hs (n+k)
  have hbefore : CappedOutputRegister.before G cap m (rho m) n v = some b := by
    simpa only [hn.1, CappedSilentExecution.reference] using hb
  have ha := CappedLocalAbsorption.absorbed G p cap hc hm n k v b hbefore
  have hq := (ha.2.2 v (self_mem_closed G v)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hn.2.1] using hq
  · simp only [hnk.1, hn.1, CappedSilentExecution.reference, ha.1, ha.2.1]
  · funext u i
    by_cases hu : v = u ∨ G.Adj v u
    · by_cases hi : i < 6
      · rw [hnk.2.2 v u i hu hi, hn.2.2 v u i hu hi]
        have hmem := (ha.2.2 u ((mem_closed G u v).mpr
          (hu.elim (fun h => Or.inl h.symm) Or.inr))).2
        rw [hmem]
      · rw [CappedSilentExecution.inactive_cache G cap m (rho m) (n+k) v u i
          (Or.inl (by omega)),
          CappedSilentExecution.inactive_cache G cap m (rho m) n v u i (Or.inl (by omega))]
    · rw [CappedSilentExecution.inactive_cache G cap m (rho m) (n+k) v u i (Or.inr hu),
        CappedSilentExecution.inactive_cache G cap m (rho m) n v u i (Or.inr hu)]
  · rw [hnk.2.1]
    exact PeriodicReplay.quiet_add (CappedReplay.notify G cap m (rho m) v) n hq k

theorem entryQuiet_run (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    entryQuiet (CappedSilentExecution.run G cap m (rho m) n) =
      (CappedSilentExecution.run G cap m (rho m) n).quiet := by
  funext v
  unfold entryQuiet
  cases hb : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 with
  | none => simp
  | some b =>
    rw [(completed_stable G p cap hc hm n 0 v b hb).1]
    rfl

theorem haltedStep_run (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    haltedStep G cap m (rho m) (CappedSilentExecution.run G cap m (rho m) n) =
      CappedSilentExecution.run G cap m (rho m) (n+1) := by
  have he : { CappedSilentExecution.run G cap m (rho m) n with
      quiet := entryQuiet (CappedSilentExecution.run G cap m (rho m) n) } =
      CappedSilentExecution.run G cap m (rho m) n := by
    rw [entryQuiet_run G p cap hc hm n]
  unfold haltedStep
  rw [he]
  apply network_ext
  · funext v
    cases hb : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 with
    | none => simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; rfl
    | some b =>
      simp only [hb, Option.isSome_some, ↓reduceIte]
      exact (completed_stable G p cap hc hm n 1 v b hb).2.1.symm
  · funext v
    cases hb : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 with
    | none => simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; rfl
    | some b =>
      simp only [hb, Option.isSome_some, ↓reduceIte]
      exact (completed_stable G p cap hc hm n 1 v b hb).2.2.1.symm
  · funext v
    cases hb : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 with
    | none => simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; rfl
    | some b =>
      simp only [hb, Option.isSome_some, ↓reduceIte]
      exact (completed_stable G p cap hc hm n 1 v b hb).2.2.2.symm

/-- Local stopping preserves the complete silent execution at every phase. -/
theorem haltedRun_eq_run (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    haltedRun G cap m (rho m) n = CappedSilentExecution.run G cap m (rho m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change haltedStep G cap m (rho m) (haltedRun G cap m (rho m) n) = _
    rw [ih, haltedStep_run G p cap hc hm n]

end Paper.Density.CappedHalting

#print axioms Paper.Density.CappedHalting.completed_stable
#print axioms Paper.Density.CappedHalting.haltedStep_run
#print axioms Paper.Density.CappedHalting.haltedRun_eq_run
