import Paper.TotalDomination.Protocol
import Paper.TotalDomination.NonintegerParameters

/-! Encoded rounding for `fv:total:noncrit`. Each private input is an
unbounded natural numerator over one positive public denominator. Capping
and the strict threshold test are local rational computations. Neither the
graph nor a vector or membership set is an executable program parameter. -/
namespace Paper.TotalDomination.EncodedRounding
open BroadcastModel
open scoped BigOperators

def fraction (denominator numerator : ℕ) : ℚ := (numerator : ℚ) / denominator

def capped (denominator numerator : ℕ) : ℚ := min 1 (fraction denominator numerator)

def threshold (a mu : ℚ) : ℚ := (1 + mu) / (2 * a)

/-- All vertices are candidates and demands; the first flag is computed. -/
def prepare (a mu : ℚ) (denominator numerator : ℕ) : Protocol.Input :=
  ⟨true, true, decide (threshold a mu < capped denominator numerator)⟩

theorem fraction_cast (denominator numerator : ℕ) :
    (fraction denominator numerator : ℝ) = (numerator : ℝ) / denominator := by
  simp only [fraction, Rat.cast_div, Rat.cast_natCast]

theorem capped_cast (denominator numerator : ℕ) :
    (capped denominator numerator : ℝ) = min 1 ((numerator : ℝ) / denominator) := by
  simp only [capped, Rat.cast_min, Rat.cast_one, fraction_cast]

theorem threshold_cast (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) :
    (threshold a mu : ℝ) = Noninteger.threshold p := by
  simp only [threshold, Rat.cast_div, Rat.cast_add, Rat.cast_one,
    Rat.cast_mul, Rat.cast_ofNat, Noninteger.threshold, ha, hmu]

/-- The real scalar package enforces exactly the paper's public conditions. -/
theorem public_conditions (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) :
    1 ≤ a ∧ 0 < mu ∧ (mu : ℝ) ≤ p.theta ∧
      (1 + (mu : ℝ)) * (1 + (mu : ℝ) - p.theta) ≤ 2 * (1 - p.theta) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (ha ▸ p.a_ge_one)
  · exact_mod_cast (hmu ▸ p.mu_pos)
  · simpa only [hmu] using p.mu_le_theta
  · simpa only [hmu] using p.admissible

theorem threshold_iff (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) (denominator numerator : ℕ) :
    threshold a mu < capped denominator numerator ↔
      Noninteger.threshold p < min 1 ((numerator : ℝ) / denominator) := by
  rw [← threshold_cast p a mu ha hmu, ← capped_cast denominator numerator]
  exact Rat.cast_lt.symm

variable {V : Type} [LinearOrder V]

/-- The runtime has only public scalars, a cutoff, and an identifier codec.
The input vector is supplied to the evaluator as private per-vertex states. -/
def program {b : ℕ} (ids : BitCode V b) (a mu : ℚ) (denominator cutoff : ℕ) :
    Program V ℕ Bool :=
  .seq (.local fun _ _ numerator => prepare a mu denominator numerator)
    (Protocol.program ids cutoff)

theorem rounds {b : ℕ} (ids : BitCode V b) (a mu : ℚ) (denominator cutoff : ℕ) :
    (program ids a mu denominator cutoff).rounds = 4 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) (a mu : ℚ) (denominator cutoff : ℕ) :
    (program ids a mu denominator cutoff).maxBits ≤ b + 1 := by
  change max 0 (Protocol.program ids cutoff).maxBits ≤ b + 1
  exact max_le (Nat.zero_le _) (Protocol.maxBits ids cutoff)

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (a mu : ℚ)
    (denominator cutoff N c : ℕ) (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program ids a mu denominator cutoff).maxBits ≤ (c + 1) * Nat.clog 2 (N + 2) :=
  (maxBits ids a mu denominator cutoff).trans (logarithmic_message_budget N b c hids).1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (ids : BitCode V b) (a mu : ℚ) (denominator cutoff : ℕ)
    (numerator : V → ℕ) : Finset V :=
  Finset.univ.filter fun v => (program ids a mu denominator cutoff).runEncoded G numerator v

theorem first_correct (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) (denominator : ℕ)
    (numerator : V → ℕ) (labels : V → ℕ)
    (hfree : ∀ r, (G.neighborFinset r).Nonempty) (v : V) :
    (prepare a mu denominator (numerator v)).first =
      decide (v ∈ TotalDomination.first G (Noninteger.input G p labels hfree
        (CoveringOptimum.cap (fun u => (numerator u : ℝ) / denominator)))) := by
  classical
  apply Bool.decide_congr
  simp only [TotalDomination.first, Noninteger.input, Finset.mem_filter,
    Finset.mem_univ, true_and, CoveringOptimum.cap]
  exact threshold_iff p a mu ha hmu denominator (numerator v)

/-- Exact encoded execution recovers the selected set in capped_rounding_bound.
The mathematical identifiers are proof-side and agree with the runtime order. -/
theorem run_eq {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) (denominator cutoff : ℕ)
    (hcutoff : cutoff = p.k + 1) (numerator : V → ℕ) (labels : V → ℕ)
    (hmono : StrictMono labels) (hfree : ∀ r, (G.neighborFinset r).Nonempty) :
    (program ids a mu denominator cutoff).runEncoded G numerator =
      fun v => decide (v ∈ TotalDomination.output G (Noninteger.input G p labels hfree
        (CoveringOptimum.cap (fun u => (numerator u : ℝ) / denominator)))) := by
  subst cutoff
  change (Protocol.program ids (p.k + 1)).runEncoded G
    (fun v => prepare a mu denominator (numerator v)) = _
  apply Protocol.run_eq G (Noninteger.input G p labels hfree
    (CoveringOptimum.cap (fun u => (numerator u : ℝ) / denominator)))
    (fun v => prepare a mu denominator (numerator v)) ids
  · intro v; simp [prepare, Noninteger.input]
  · intro v; simp [prepare, Noninteger.input]
  · exact first_correct G p a mu ha hmu denominator numerator labels hfree
  · exact hmono

theorem output_eq {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) (denominator cutoff : ℕ)
    (hcutoff : cutoff = p.k + 1) (numerator : V → ℕ) (labels : V → ℕ)
    (hmono : StrictMono labels) (hfree : ∀ r, (G.neighborFinset r).Nonempty) :
    output G ids a mu denominator cutoff numerator =
      TotalDomination.output G (Noninteger.input G p labels hfree
        (CoveringOptimum.cap (fun u => (numerator u : ℝ) / denominator))) := by
  unfold output
  rw [run_eq G ids p a mu ha hmu denominator cutoff hcutoff numerator labels hmono hfree]
  ext v
  simp

/-- Actual four-round encoded rounding bounds the original, uncapped mass.
There is no upper bound on the private numerators. -/
theorem rounding_bound {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters) (a mu : ℚ)
    (ha : p.a = (a : ℝ)) (hmu : p.mu = (mu : ℝ)) (denominator cutoff : ℕ)
    (hdenominator : 0 < denominator) (hcutoff : cutoff = p.k + 1)
    (numerator : V → ℕ) (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ r, (G.neighborFinset r).Nonempty)
    (hden : Incidence.InducedDensityBound G (a : ℝ))
    (hcover : ∀ r, 1 ≤ ∑ v ∈ G.neighborFinset r, (numerator v : ℝ) / denominator) :
    (∀ r, ∃ v ∈ output G ids a mu denominator cutoff numerator, G.Adj r v) ∧
      ((output G ids a mu denominator cutoff numerator).card : ℝ) ≤
        (2 * (a : ℝ) - (mu : ℝ)) * ∑ v, (numerator v : ℝ) / denominator := by
  rw [output_eq G ids p a mu ha hmu denominator cutoff hcutoff numerator labels hmono hfree]
  have hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ
      (fun v => (numerator v : ℝ) / denominator) := by
    refine ⟨?_, fun r _ => hcover r⟩
    intro v
    exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hdenominator.le)
  have hd : Incidence.InducedDensityBound G p.a := by simpa only [ha] using hden
  simpa only [ha, hmu] using
    Noninteger.capped_rounding_bound G p labels hfree
      (fun v => (numerator v : ℝ) / denominator) hd hx

/-- The same ID budget includes the complete adapter and all four broadcasts. -/
theorem resources {b : ℕ} (ids : BitCode V b) (a mu : ℚ) (denominator cutoff c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids a mu denominator cutoff).rounds = 4 ∧
      (program ids a mu denominator cutoff).maxBits ≤
        (c + 1) * Nat.clog 2 (Fintype.card V + 2) :=
  ⟨rounds ids a mu denominator cutoff,
    logarithmic_bits ids a mu denominator cutoff (Fintype.card V) c hids⟩

end Paper.TotalDomination.EncodedRounding

#print axioms Paper.TotalDomination.EncodedRounding.threshold_cast
#print axioms Paper.TotalDomination.EncodedRounding.run_eq
#print axioms Paper.TotalDomination.EncodedRounding.rounding_bound
#print axioms Paper.TotalDomination.EncodedRounding.resources
