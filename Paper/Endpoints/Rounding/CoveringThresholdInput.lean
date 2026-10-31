import Paper.Endpoints.Rounding.CoveringRoundingCost

/-! Numerical threshold initialization uses only the local numerator and a
public positive denominator. No fractional values are transmitted. -/
namespace Paper.CoveringThresholdInput

open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
attribute [local instance 10] Classical.propDecidable

structure Input (V : Type) (B : ℕ) where
  demand : Bool
  cost : Fin (B + 1)
  candidates : Finset V
  numerator : ℕ

def prepare {B : ℕ} (t q : ℕ) (s : Input V B) : CoveringRoundingProtocol.Input V B :=
  ⟨decide (q ≤ t * s.numerator), s.demand, s.cost, s.candidates⟩

def program {b : ℕ} (ids : BitCode V b) (B t q : ℕ) :
    Program V (Input V B) GeneralCoveringRequests.Output :=
  .seq (.local (fun _ _ s => prepare t q s))
    (CoveringRoundingProtocol.normalizedProgram ids B)

omit [Fintype V] in
theorem rounds {b : ℕ} (ids : BitCode V b) (B t q : ℕ) :
    (program ids B t q).rounds = 3 := rfl

omit [Fintype V] in
theorem maxBits {b : ℕ} (ids : BitCode V b) (B t q : ℕ) :
    (program ids B t q).maxBits ≤ max (B + 2) (b + 1) := by
  change max 0 (CoveringRoundingProtocol.normalizedProgram ids B).maxBits ≤ _
  exact max_le (Nat.zero_le _) (CoveringRoundingProtocol.normalized_maxBits ids B)

theorem threshold_iff (t q n : ℕ) (ht : 0 < t) (hq : 0 < q) :
    1 / (t : ℝ) ≤ (n : ℝ) / q ↔ q ≤ t * n := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ htR hqR, one_mul, mul_comm]
  exact_mod_cast (Iff.rfl : q ≤ t * n ↔ q ≤ t * n)

omit [Fintype V] [LinearOrder V] in
theorem selected_iff {B : ℕ} (t q : ℕ) (ht : 0 < t) (hq : 0 < q)
    (s : Input V B) :
    (prepare t q s).selected = true ↔ 1 / (t : ℝ) ≤ (s.numerator : ℝ) / q := by
  simp only [prepare, decide_eq_true_eq]
  exact (threshold_iff t q s.numerator ht hq).symm

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem residual_eq {B : ℕ} (t q : ℕ) (ht : 0 < t) (hq : 0 < q)
    (s : V → Input V B) :
    CoveringRoundingProtocol.residual (fun v => prepare t q (s v)) =
      (Finset.univ.filter (fun r => (s r).demand = true)).filter
        (fun r => ∀ v ∈ (s r).candidates, (s v).numerator / (q : ℝ) < 1 / t) := by
  classical
  ext r
  have hs (v : V) : q ≤ t * (s v).numerator ↔
      1 / (t : ℝ) ≤ (s v).numerator / (q : ℝ) :=
    (threshold_iff t q (s v).numerator ht hq).symm
  simp [CoveringRoundingProtocol.residual, prepare,
    Finset.eq_empty_iff_forall_notMem, hs, not_le]

theorem output_image {b B : ℕ} (ids : BitCode V b) (t q : ℕ) (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    (Finset.univ.filter (fun v => ((program ids B t q).runEncoded G s v).selected = true)) =
      (Finset.univ.filter (fun v => q ≤ t * (s v).numerator)) ∪
        (CoveringRoundingProtocol.residual (fun v => prepare t q (s v))).image
          (CoveringRoundingCost.chosen (fun v => prepare t q (s v))) := by
  have h := CoveringRoundingCost.normalized_output_image G ids
    (fun v => prepare t q (s v)) hlocal hrows
  simpa only [program, Program.runEncoded_eq_run, Program.run, prepare,
    decide_eq_true_eq] using h

theorem output_covers {b B : ℕ} (ids : BitCode V b) (t q : ℕ) (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (r : V) (hr : (s r).demand = true) :
    ∃ v ∈ (s r).candidates, ((program ids B t q).runEncoded G s v).selected = true := by
  have he := output_image G ids t q s hlocal hrows
  by_cases hh : ∃ v ∈ (s r).candidates, q ≤ t * (s v).numerator
  · obtain ⟨v, hv, hs⟩ := hh
    refine ⟨v, hv, ?_⟩
    have hm : v ∈ Finset.univ.filter (fun v =>
        ((program ids B t q).runEncoded G s v).selected = true) := by
      rw [he]
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    exact (Finset.mem_filter.mp hm).2
  · let p := fun v => prepare t q (s v)
    have hrW : r ∈ CoveringRoundingProtocol.residual p := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, ?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvC := (Finset.mem_inter.mp hv).1
      have hvS := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
      exact hh ⟨v, hvC, by simpa only [p, prepare, decide_eq_true_eq] using hvS⟩
    have hc := CoveringRoundingCost.chosen_spec p r (hrows r hr)
    refine ⟨CoveringRoundingCost.chosen p r, hc.2.1, ?_⟩
    have hm : CoveringRoundingCost.chosen p r ∈ Finset.univ.filter (fun v =>
        ((program ids B t q).runEncoded G s v).selected = true) := by
      rw [he]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hrW, rfl⟩)
    exact (Finset.mem_filter.mp hm).2

end Paper.CoveringThresholdInput

#print axioms Paper.CoveringThresholdInput.rounds
#print axioms Paper.CoveringThresholdInput.maxBits
#print axioms Paper.CoveringThresholdInput.threshold_iff
#print axioms Paper.CoveringThresholdInput.selected_iff
#print axioms Paper.CoveringThresholdInput.residual_eq
#print axioms Paper.CoveringThresholdInput.output_image
#print axioms Paper.CoveringThresholdInput.output_covers
