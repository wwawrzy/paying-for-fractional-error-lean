import Paper.TotalDomination.Protocol
import Paper.TotalDomination.Noninteger

/-! Standalone rounding of arbitrary real feasible inputs in the model of
unrestricted local maps with exact private comparisons. The comparison uses
`Classical.propDecidable`; no real value is transmitted. `EncodedRounding`
separately provides the effective rational-input implementation. -/

namespace Paper.TotalDomination.RealInputRounding

open BroadcastModel
open scoped BigOperators

/-- Only the local capped threshold decision enters the broadcast protocol. -/
noncomputable def prepare (threshold x : ℝ) : Protocol.Input := by
  letI := Classical.propDecidable
  exact ⟨true, true, decide (threshold < min 1 x)⟩

variable {V : Type} [LinearOrder V]

/-- Public runtime arguments contain no graph or input vector. -/
noncomputable def program {b : ℕ} (ids : BitCode V b) (threshold : ℝ) (cutoff : ℕ) :
    Program V ℝ Bool :=
  .seq (.local fun _ _ x => prepare threshold x) (Protocol.program ids cutoff)

theorem rounds {b : ℕ} (ids : BitCode V b) (threshold : ℝ) (cutoff : ℕ) :
    (program ids threshold cutoff).rounds = 4 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) (threshold : ℝ) (cutoff : ℕ) :
    (program ids threshold cutoff).maxBits ≤ b + 1 := by
  change max 0 (Protocol.program ids cutoff).maxBits ≤ b + 1
  exact max_le (Nat.zero_le _) (Protocol.maxBits ids cutoff)

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (threshold : ℝ)
    (cutoff N c : ℕ) (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program ids threshold cutoff).maxBits ≤ (c + 1) * Nat.clog 2 (N + 2) :=
  (maxBits ids threshold cutoff).trans (logarithmic_message_budget N b c hids).1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def output {b : ℕ} (ids : BitCode V b) (threshold : ℝ) (cutoff : ℕ)
    (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => (program ids threshold cutoff).runEncoded G x v

/-- The private real comparison produces precisely the mathematical first set. -/
theorem first_correct (p : Noninteger.Parameters) (x : V → ℝ) (labels : V → ℕ)
    (hfree : ∀ r, (G.neighborFinset r).Nonempty) (v : V) :
    (prepare (Noninteger.threshold p) (x v)).first =
      decide (v ∈ TotalDomination.first G
        (Noninteger.input G p labels hfree (CoveringOptimum.cap x))) := by
  classical
  apply Bool.decide_congr
  simp only [TotalDomination.first, Noninteger.input, Finset.mem_filter,
    Finset.mem_univ, true_and, CoveringOptimum.cap]

theorem run_eq {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters)
    (threshold : ℝ) (cutoff : ℕ) (hthreshold : threshold = Noninteger.threshold p)
    (hcutoff : cutoff = p.k + 1) (x : V → ℝ) (labels : V → ℕ)
    (hmono : StrictMono labels) (hfree : ∀ r, (G.neighborFinset r).Nonempty) :
    (program ids threshold cutoff).runEncoded G x =
      fun v => decide (v ∈ TotalDomination.output G
        (Noninteger.input G p labels hfree (CoveringOptimum.cap x))) := by
  classical
  subst threshold
  subst cutoff
  change (Protocol.program ids (p.k + 1)).runEncoded G
    (fun v => prepare (Noninteger.threshold p) (x v)) = _
  apply Protocol.run_eq G (Noninteger.input G p labels hfree (CoveringOptimum.cap x))
    (fun v => prepare (Noninteger.threshold p) (x v)) ids
  · intro v; simp [prepare, Noninteger.input]
  · intro v; simp [prepare, Noninteger.input]
  · exact first_correct G p x labels hfree
  · exact hmono

theorem output_eq {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters)
    (threshold : ℝ) (cutoff : ℕ) (hthreshold : threshold = Noninteger.threshold p)
    (hcutoff : cutoff = p.k + 1) (x : V → ℝ) (labels : V → ℕ)
    (hmono : StrictMono labels) (hfree : ∀ r, (G.neighborFinset r).Nonempty) :
    output G ids threshold cutoff x = TotalDomination.output G
      (Noninteger.input G p labels hfree (CoveringOptimum.cap x)) := by
  classical
  unfold output
  rw [run_eq G ids p threshold cutoff hthreshold hcutoff x labels hmono hfree]
  ext v
  simp

/-- Every feasible real vector is rounded with the exact coefficient and
four short broadcasts. Increasing mathematical labels are constructed here;
they are neither a runtime argument nor an additional input hypothesis. -/
theorem rounding_bound {b : ℕ} (ids : BitCode V b) (p : Noninteger.Parameters)
    (threshold : ℝ) (cutoff : ℕ) (hthreshold : threshold = Noninteger.threshold p)
    (hcutoff : cutoff = p.k + 1) (x : V → ℝ)
    (hfree : ∀ r, (G.neighborFinset r).Nonempty)
    (hden : Incidence.InducedDensityBound G p.a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ x) :
    (∀ r, ∃ v ∈ output G ids threshold cutoff x, G.Adj r v) ∧
      ((output G ids threshold cutoff x).card : ℝ) ≤ (2 * p.a - p.mu) * ∑ v, x v ∧
      (program ids threshold cutoff).rounds = 4 ∧
      (program ids threshold cutoff).maxBits ≤ b + 1 := by
  classical
  let labels : V → ℕ := fun v => ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val
  have hmono : StrictMono labels := by
    intro u v huv
    exact (Fintype.orderIsoFinOfCardEq V rfl).symm.strictMono huv
  have heq := output_eq G ids p threshold cutoff hthreshold hcutoff x labels hmono hfree
  obtain ⟨hdom, hbound⟩ := Noninteger.capped_rounding_bound G p labels hfree x hden hx
  refine ⟨?_, ?_, rounds ids threshold cutoff, maxBits ids threshold cutoff⟩
  · simpa only [heq] using hdom
  · simpa only [heq] using hbound

/-- The identifier budget includes the local adapter and the whole protocol. -/
theorem resources {b : ℕ} (ids : BitCode V b) (threshold : ℝ) (cutoff c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids threshold cutoff).rounds = 4 ∧
      (program ids threshold cutoff).maxBits ≤ (c + 1) * Nat.clog 2 (Fintype.card V + 2) :=
  ⟨rounds ids threshold cutoff,
    logarithmic_bits ids threshold cutoff (Fintype.card V) c hids⟩

end Paper.TotalDomination.RealInputRounding

#print axioms Paper.TotalDomination.RealInputRounding.run_eq
#print axioms Paper.TotalDomination.RealInputRounding.output_eq
#print axioms Paper.TotalDomination.RealInputRounding.rounding_bound
#print axioms Paper.TotalDomination.RealInputRounding.resources
