import Paper.Solver.Density.CappedSilentResources
import Paper.Solver.Density.CappedRegisteredCompletion
import Paper.Solver.Density.CappedSilentParameters

/-! A graph-uniform mathematical and resource interface for the actual silent
network loop. Public parameters are chosen before every finite graph. Degree
bounds determine analysis deadlines only. A separate local-stop wrapper is
needed to turn this silent execution into explicit halted local states. -/
namespace Paper.Density.CappedSilentOutput
open SevenFoundation
open CappedUniformParameters (cap rho)

/-- Output, permanent silence, width and elapsed rounds of the actual loop. -/
def HasSilentOutputGuarantee (a : ℚ) (m : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Incidence.InducedDensityBound G (a : ℝ) →
    ∃ D : Finset V, dominates G D ∧ (D.card : ℝ) ≤ (2*(a : ℝ)+1)*fractionalNumber G ∧
      ∀ (Delta : ℕ), (∀ v, G.degree v ≤ Delta) → Delta ≤ Fintype.card V →
        (∀ v, ∃ b : Bool,
          ((CappedSilentExecution.run G (cap a) m (rho m)
            (CappedGrowth.timeBound m Delta + 1)).values v).2 = some b ∧
          (b = true ↔ v ∈ D)) ∧
        (∀ k i v, CappedSilentResources.phaseWire G (cap a) m (rho m)
          (CappedGrowth.timeBound m Delta + 1 + k) i v = none) ∧
        (∀ n ≤ CappedGrowth.timeBound m Delta, ∀ i < 6, ∀ v,
          PrefixBroadcast.Program.sentBits
            (CappedSilentResources.phaseWire G (cap a) m (rho m) n i v) ≤
              (2*m+5)*Nat.clog 2 (Fintype.card V+2)) ∧
        (CappedOutputRegister.startup (V := V) (cap a)).rounds +
          (CappedGrowth.timeBound m Delta + 1) *
            (CappedOutputRegister.phase (V := V) (cap a) m (rho m)).rounds ≤
          (6*m+7)*(1+(Nat.clog 2 (max 2 Delta))^2)

/-- Rational density alone determines the public parameter of the single loop. -/
theorem parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2*a) :
    ∃ m : ℕ, 0 < m ∧ HasSilentOutputGuarantee a m := by
  obtain ⟨p, m, hpa, hm, hc, hr⟩ := CappedUniformParameters.parameters a ha hnoninteger
  have hrho : 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m := by
    simpa only [CappedUniformParameters.rho_cast] using hr
  have hcap : 0 ≤ cap a := (CappedUniformParameters.cap_pos a ha).le
  have hscale : CappedCounterState.scale m * rho m ≤ 1 :=
    (CappedSilentParameters.scale_mul_rho hm).le
  refine ⟨m, hm, ?_⟩
  intro V _ _ G _ hden
  have hd : Incidence.InducedDensityBound G p.a := by simpa only [hpa] using hden
  let D := CappedCompletion.output G p (cap a) hc hm
  have hbound := CappedCompletion.domination_bound G p (cap a) hc hm hd hrho
  refine ⟨D, hbound.1, ?_, ?_⟩
  · simpa only [hpa] using hbound.2
  · intro Delta hdegree hD
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      let b := (CappedCompletion.observed G (cap a) m
        (CappedCompletion.firstTime G p (cap a) hc hm v) v).output
      refine ⟨b, ?_, ?_⟩
      · rw [CappedSilentExecution.run_values G (cap a) hm hcap (rho m) hscale]
        change CappedOutputRegister.reported G (cap a) m (rho m)
          (CappedGrowth.timeBound m Delta) v = some b
        have hb := CappedRegisteredCompletion.actual_local_output G p (cap a) hc hm v _
          (CappedCompletion.firstTime_le G p (cap a) hc hm Delta hdegree v)
        simpa only [CappedOutputRegister.schedule_run] using hb
      · simp only [D, b, CappedCompletion.output, Finset.mem_filter, Finset.mem_univ, true_and]
    · intro k i v
      exact CappedSilentResources.phaseWire_none_after_bound G p (cap a) hc hm Delta hdegree k i v
    · intro n hn i hi v
      simpa only [Nat.mul_zero, Nat.add_zero] using
        CappedSilentResources.phaseWire_bits G (cap a) hm hcap (rho m) hscale
          n i v hi Delta 0 hdegree hD (by simpa using hn)
    · change 1 + (CappedGrowth.timeBound m Delta + 1) *
        (CappedOutputRegister.phase (V := V) (cap a) m (rho m)).rounds ≤ _
      rw [CappedOutputRegister.phase_rounds]
      simpa only [Nat.mul_comm] using CappedSilentParameters.silent_rounds_bound m Delta

end Paper.Density.CappedSilentOutput

#print axioms Paper.Density.CappedSilentOutput.parameters
