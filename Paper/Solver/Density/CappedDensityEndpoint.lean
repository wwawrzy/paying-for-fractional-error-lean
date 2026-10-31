import Paper.Solver.Density.CappedSilentOutput
import Paper.Solver.Density.CappedHalting
import Paper.Solver.Density.CappedStartupResources

/-! Exact-density output and resources of the locally halted execution.
Public parameters precede the graph. Degree bounds occur only in analysis;
the runtime stops each vertex using its own private output register. -/
namespace Paper.Density.CappedDensityEndpoint
open SevenFoundation
open CappedUniformParameters (cap rho)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Physical transmissions use the same phase-entry quiet flags as haltedStep. -/
def haltedPhaseWire (cap : ℚ) (m : ℕ) (threshold : ℚ) (n i : ℕ) (v : V) :
    Option (List Bool) :=
  let s := CappedHalting.haltedRun G cap m threshold n
  (CappedOutputRegister.phase cap m threshold).cachedSent G
    (CappedHalting.entryQuiet s) s.values s.memory 0 i v

theorem haltedPhaseWire_eq (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m)
    (n i : ℕ) (v : V) :
    haltedPhaseWire G cap m (rho m) n i v =
      CappedSilentResources.phaseWire G cap m (rho m) n i v := by
  simp only [haltedPhaseWire, CappedSilentResources.phaseWire,
    CappedHalting.haltedRun_eq_run G p cap hc hm n,
    CappedHalting.entryQuiet_run G p cap hc hm n]

/-- A completed vertex sends nothing, even for arbitrary parameters or slots. -/
theorem haltedPhaseWire_none_of_completed (cap : ℚ) (m : ℕ) (threshold : ℚ)
    (n i : ℕ) (v : V) (b : Bool)
    (hb : ((CappedHalting.haltedRun G cap m threshold n).values v).2 = some b) :
    haltedPhaseWire G cap m threshold n i v = none := by
  apply PrefixBroadcast.Program.cachedSent_quiet
  simp [CappedHalting.entryQuiet, hb]

/-- Full local persistence includes all receiver slots and the quiet flag. -/
def LocallyHalts (cap : ℚ) (m : ℕ) (threshold : ℚ) : Prop :=
  ∀ n v b, ((CappedHalting.haltedRun G cap m threshold n).values v).2 = some b →
    (CappedHalting.haltedRun G cap m threshold n).quiet v = true ∧
    ∀ k,
      (CappedHalting.haltedRun G cap m threshold (n+k)).values v =
        (CappedHalting.haltedRun G cap m threshold n).values v ∧
      (CappedHalting.haltedRun G cap m threshold (n+k)).memory v =
        (CappedHalting.haltedRun G cap m threshold n).memory v ∧
      (CappedHalting.haltedRun G cap m threshold (n+k)).quiet v =
        (CappedHalting.haltedRun G cap m threshold n).quiet v ∧
      ∀ i, haltedPhaseWire G cap m threshold (n+k) i v = none

theorem locallyHalts (p : NeighborhoodSlack.Parameters) (cap : ℚ)
    (hc : (cap : ℝ) = CappedConvergence.cap p) {m : ℕ} (hm : 0 < m) :
    LocallyHalts G cap m (rho m) := by
  intro n v b hb
  have hb' : ((CappedSilentExecution.run G cap m (rho m) n).values v).2 = some b := by
    simpa only [CappedHalting.haltedRun_eq_run G p cap hc hm n] using hb
  have stable (k : ℕ) := CappedHalting.completed_stable G p cap hc hm n k v b hb'
  have hquiet : (CappedHalting.haltedRun G cap m (rho m) n).quiet v = true := by
    simpa only [CappedHalting.haltedRun_eq_run G p cap hc hm n] using (stable 0).1
  refine ⟨hquiet, ?_⟩
  intro k
  have hv : (CappedHalting.haltedRun G cap m (rho m) (n+k)).values v =
      (CappedHalting.haltedRun G cap m (rho m) n).values v := by
    simpa only [CappedHalting.haltedRun_eq_run G p cap hc hm] using (stable k).2.1
  refine ⟨hv, ?_, ?_, ?_⟩
  · simpa only [CappedHalting.haltedRun_eq_run G p cap hc hm] using (stable k).2.2.1
  · rw [hquiet, CappedHalting.haltedRun_eq_run G p cap hc hm]
    exact (stable k).2.2.2
  · intro i
    apply haltedPhaseWire_none_of_completed G cap m (rho m) (n+k) i v b
    rw [hv]
    exact hb

/-- All guarantees concern the actual halted loop and its physical wires.
The startup is the program defining haltedRun's initial state. -/
def HasDensityGuarantee (a : ℚ) (m : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Incidence.InducedDensityBound G (a : ℝ) →
    ∃ D : Finset V, dominates G D ∧ (D.card : ℝ) ≤ (2*(a : ℝ)+1)*fractionalNumber G ∧
      LocallyHalts G (cap a) m (rho m) ∧
      (CappedOutputRegister.startup (cap a)).maxBits G (fun _ => PUnit.unit) ≤
        (2*m+5)*Nat.clog 2 (Fintype.card V+2) ∧
      ∀ (Delta : ℕ), (∀ v, G.degree v ≤ Delta) → Delta ≤ Fintype.card V →
        (∀ v, ∃ b : Bool,
          ((CappedHalting.haltedRun G (cap a) m (rho m)
            (CappedGrowth.timeBound m Delta + 1)).values v).2 = some b ∧
          (b = true ↔ v ∈ D)) ∧
        (∀ k i v, haltedPhaseWire G (cap a) m (rho m)
          (CappedGrowth.timeBound m Delta + 1 + k) i v = none) ∧
        (∀ n i, i < 6 → ∀ v, PrefixBroadcast.Program.sentBits
          (haltedPhaseWire G (cap a) m (rho m) n i v) ≤
            (2*m+5)*Nat.clog 2 (Fintype.card V+2)) ∧
        (CappedOutputRegister.startup (V := V) (cap a)).rounds +
          6 * (CappedGrowth.timeBound m Delta + 1) ≤
          (6*m+7)*(1+(Nat.clog 2 (max 2 Delta))^2)

/-- Rational density determines one public parameter before every finite graph.
No supplied stopping certificate or degree bound is an algorithm input. -/
theorem parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2*a) :
    ∃ m : ℕ, 0 < m ∧ HasDensityGuarantee a m := by
  obtain ⟨p, _, _, _, hc, _⟩ := CappedUniformParameters.parameters a ha hnoninteger
  obtain ⟨m, hm, hsilent⟩ := CappedSilentOutput.parameters a ha hnoninteger
  refine ⟨m, hm, ?_⟩
  intro V _ _ G _ hden
  obtain ⟨D, hdom, hsize, hrun⟩ := hsilent V G hden
  refine ⟨D, hdom, hsize, locallyHalts G p (cap a) hc hm,
    CappedStartupResources.startup_bits G (cap a) m, ?_⟩
  intro Delta hdegree hD
  obtain ⟨hout, hnone, hbits, hrounds⟩ := hrun Delta hdegree hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [CappedHalting.haltedRun_eq_run G p (cap a) hc hm] using hout
  · simpa only [haltedPhaseWire_eq G p (cap a) hc hm] using hnone
  · intro n i hi v
    rw [haltedPhaseWire_eq G p (cap a) hc hm]
    by_cases hn : n ≤ CappedGrowth.timeBound m Delta
    · exact hbits n hn i hi v
    · have he : CappedGrowth.timeBound m Delta + 1 +
          (n - (CappedGrowth.timeBound m Delta + 1)) = n :=
        Nat.add_sub_of_le (by omega)
      have hwire := hnone (n - (CappedGrowth.timeBound m Delta + 1)) i v
      rw [he] at hwire
      rw [hwire]
      exact Nat.zero_le _
  · simpa only [CappedOutputRegister.phase_rounds, Nat.mul_comm] using hrounds

end Paper.Density.CappedDensityEndpoint

#print axioms Paper.Density.CappedDensityEndpoint.haltedPhaseWire_eq
#print axioms Paper.Density.CappedDensityEndpoint.locallyHalts
#print axioms Paper.Density.CappedDensityEndpoint.parameters
