import Paper.Solver.Density.CappedRegisteredCompletion
import Paper.Solver.Density.CappedRoundComplexity

/-! A uniform source interface for completed local output registers.
The public growth parameter precedes every graph. Degree bounds appear only
in guarantees about prefixes of the single repeated protocol. This result
does not yet assert that completed vertices cease transmitting. -/
namespace Paper.Density.CappedUniformOutput
open SevenFoundation
open CappedUniformParameters (cap rho)

def HasLocalOutputGuarantee (a : ℚ) (m : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Incidence.InducedDensityBound G (a : ℝ) →
    ∃ D : Finset V, dominates G D ∧ (D.card : ℝ) ≤ (2*(a : ℝ)+1)*fractionalNumber G ∧
      ∀ (Delta : ℕ), (∀ v, G.degree v ≤ Delta) → Delta ≤ Fintype.card V →
        (∀ v, ∃ b : Bool,
          ((CappedOutputRegister.schedule (cap a) m (rho m)
            (CappedGrowth.timeBound m Delta)).run G (fun _ => PUnit.unit) v).2 = some b ∧
          (b = true ↔ v ∈ D)) ∧
        (CappedOutputRegister.schedule (V := V) (cap a) m (rho m)
          (CappedGrowth.timeBound m Delta)).rounds ≤
          (6*m+5)*(1+(Nat.clog 2 (max 2 Delta))^2) ∧
        (∀ n ≤ CappedGrowth.timeBound m Delta,
          (CappedOutputRegister.schedule (cap a) m (rho m) n).maxBits G
            (fun _ => PUnit.unit) ≤ (2*m+5)*Nat.clog 2 (Fintype.card V+2))

/-- All constants are chosen from rational density alone, before the graph,
its order, and the maximum degree used to analyze completion time. -/
theorem parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2*a) :
    ∃ m : ℕ, 0 < m ∧ HasLocalOutputGuarantee a m := by
  obtain ⟨p, m, hpa, hm, hc, hr⟩ := CappedUniformParameters.parameters a ha hnoninteger
  have hrho : 2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*CappedGrowth.rho m := by
    simpa only [CappedUniformParameters.rho_cast] using hr
  refine ⟨m, hm, ?_⟩
  intro V _ _ G _ hden
  have hd : Incidence.InducedDensityBound G p.a := by simpa only [hpa] using hden
  let D := CappedCompletion.output G p (cap a) hc hm
  have hbound := CappedCompletion.domination_bound G p (cap a) hc hm hd hrho
  refine ⟨D, hbound.1, ?_, ?_⟩
  · simpa only [hpa] using hbound.2
  · intro Delta hdegree hD
    refine ⟨?_, ?_, ?_⟩
    · intro v
      let b := (CappedCompletion.observed G (cap a) m
        (CappedCompletion.firstTime G p (cap a) hc hm v) v).output
      refine ⟨b, ?_, ?_⟩
      · exact CappedRegisteredCompletion.actual_local_output G p (cap a) hc hm v _
          (CappedCompletion.firstTime_le G p (cap a) hc hm Delta hdegree v)
      · simp only [D, b, CappedCompletion.output, Finset.mem_filter, Finset.mem_univ, true_and]
    · rw [CappedOutputRegister.schedule_rounds]
      have hb := CappedRoundComplexity.rounds_bound m Delta
      omega
    · intro n hn
      simpa only [Nat.mul_zero, Nat.add_zero] using
        CappedOutputRegister.schedule_bits G (cap a) m (rho m) n Delta 0 hdegree hD
          (by simpa using hn)

end Paper.Density.CappedUniformOutput
#print axioms Paper.Density.CappedUniformOutput.parameters
