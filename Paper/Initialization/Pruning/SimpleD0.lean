import Paper.Initialization.Pruning.SimpleBroadcast
import Paper.Certificates.Counting.HumanDependencies
import Paper.Communication.EncodedProgram

/-! The current D0 theorem for every fixed rational minor-density bound.
All parameters are chosen before the graph. The result refers to the actual
encoded marked-list program, with h = 3 ceil(a) and T = ceil(a) + 1. -/
namespace Paper.SimpleD0
open BroadcastModel SevenFoundation
open scoped BigOperators

def degree (a : ℚ) : ℕ := Nat.ceil a
def threshold (a : ℚ) : ℕ := 3 * degree a
def passes (a : ℚ) : ℕ := degree a + 1
def parameter (a : ℚ) : ℕ := Nat.ceil (2 * (threshold a : ℚ) * (a + threshold a))
def constant (a : ℚ) : ℕ :=
  passes a * (passes a + 1) * threshold a * (MarkedLists.factor (parameter a) (threshold a) + 1)

theorem degree_bound (a : ℚ) : (a : ℝ) ≤ degree a := by
  have h := Nat.le_ceil a
  exact_mod_cast h

theorem degree_pos (a : ℚ) (ha : 1 ≤ a) : 1 ≤ degree a := by
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have h : (1 : ℝ) ≤ degree a := ha'.trans (degree_bound a)
  exact_mod_cast h

theorem degree_real (a : ℚ) : Nat.ceil (a : ℝ) = degree a := by
  apply Nat.le_antisymm
  · exact Nat.ceil_le.mpr (degree_bound a)
  · apply Nat.ceil_le.mpr
    have h := Nat.le_ceil (a : ℝ)
    exact_mod_cast h

theorem parameter_bound (a : ℚ) :
    2 * (threshold a : ℝ) * ((a : ℝ) + threshold a) ≤ parameter a := by
  have h : 2 * (threshold a : ℚ) * (a + threshold a) ≤ (parameter a : ℚ) :=
    Nat.le_ceil (2 * (threshold a : ℚ) * (a + threshold a))
  exact_mod_cast h

variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (a : ℚ) : Program V Bool Bool :=
  SimpleBroadcast.program C (threshold a) (parameter a) (passes a)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (C : BitCode V b) (a : ℚ) (R : Finset V) : Finset V :=
  Finset.univ.filter (fun v => (program C a).runEncoded G (fun u => decide (u ∈ R)) v = true)

theorem output_eq {b : ℕ} (C : BitCode V b) (a : ℚ) (R : Finset V) :
    output G C a R =
      PruningRun.union G (SimpleInitializer.run G (threshold a) (parameter a) (passes a) R) ∪
        SimpleInitializer.state G (threshold a) (parameter a) R (passes a) := by
  ext v
  simp only [output, Program.runEncoded_eq_run, Finset.mem_filter, Finset.mem_univ, true_and,
    program, SimpleBroadcast.correct G C (threshold a) (parameter a) (passes a) R,
    decide_eq_true_eq]
  unfold PruningRun.union SimpleInitializer.run
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]

/-- The exact current initializer bound, for any set R to be dominated and
any integral cover O. No list-density, matching, path or residual certificate
is supplied as a hypothesis. -/
theorem spec {b : ℕ} (C : BitCode V b) (a : ℚ) (ha : 1 ≤ a)
    (hden : MinorDensity.Bound G (a : ℝ)) (R O : Finset V) (hO : R ⊆ covered G O) :
    R ⊆ covered G (output G C a R) ∧ (output G C a R).card ≤ constant a * O.card := by
  have hass := SimpleInitializer.assembled_bound G (degree a) (parameter a)
    (degree_pos a ha) (a : ℝ) (by exact_mod_cast ha) (degree_bound a) hden
    (by simpa only [threshold, Nat.cast_mul, Nat.cast_ofNat] using parameter_bound a) R O
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hass
  have h := hass hO
  rw [output_eq]
  refine ⟨h.1, ?_⟩
  have hc :
      ((PruningRun.union G (SimpleInitializer.run G (threshold a) (parameter a) (passes a) R) ∪
        SimpleInitializer.state G (threshold a) (parameter a) R (passes a)).card : ℝ) ≤
        (constant a : ℝ) * O.card := by
    simpa [constant, passes, threshold, Nat.cast_mul, Nat.cast_add, add_assoc] using h.2
  exact_mod_cast hc

/-- The weighted partial fractional interface used by the rest of the paper.
Costs affect the benchmark only; the executed initializer uses the residual bits. -/
theorem weighted_spec {b : ℕ} (C : BitCode V b) (a : ℚ) (ha : 1 ≤ a)
    (hden : MinorDensity.Bound G (a : ℝ)) (R : Finset V)
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) :
    R ⊆ covered G (output G C a R) ∧
      ((output G C a R).card : ℝ) ≤
        (constant a : ℝ) * (2 * (degree a : ℝ) + 1) * PartialOptimum.number G R c := by
  obtain ⟨O, hO, hcost⟩ := HumanDependencies.integral_optimum G (a : ℝ)
    (by exact_mod_cast ha) hden R c (fun v => zero_le_one.trans (hc v))
  rw [degree_real] at hcost
  have hs := spec G C a ha hden R O hO
  have hcard : (O.card : ℝ) ≤ ∑ v ∈ O, c v := by
    calc
      _ = ∑ _v ∈ O, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hc v)
  have hb : ((output G C a R).card : ℝ) ≤ (constant a : ℝ) * O.card := by
    exact_mod_cast hs.2
  refine ⟨hs.1, hb.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hcard.trans hcost)
    (Nat.cast_nonneg (constant a) : (0 : ℝ) ≤ constant a)
  simpa only [mul_assoc] using hh

theorem rounds {b : ℕ} (C : BitCode V b) (a : ℚ) :
    (program C a).rounds = passes a * (4 + 2 * threshold a) :=
  SimpleBroadcast.rounds C (threshold a) (parameter a) (passes a)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (a : ℚ) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n+2)) :
    (program C a).maxBits ≤ (1 + threshold a * (c+1)) * Nat.clog 2 (n+2) :=
  SimpleBroadcast.logarithmic_bits C (threshold a) (parameter a) (passes a) n c hids

end Paper.SimpleD0

#print axioms Paper.SimpleD0.spec
#print axioms Paper.SimpleD0.weighted_spec
#print axioms Paper.SimpleD0.rounds
#print axioms Paper.SimpleD0.logarithmic_bits
