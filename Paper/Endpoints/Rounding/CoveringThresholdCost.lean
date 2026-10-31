import Paper.Endpoints.Rounding.CoveringThresholdInput

/-! Exact cost of the numerical threshold program on arbitrary local rows.
Only rows of actual demands enter the incidence density hypothesis. -/
namespace Paper.CoveringThresholdCost

open BroadcastModel SevenFoundation OrientedNeighborhoods HallOrientation
open CoveringThresholdInput GeneralCoveringRounding
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

def demands {B : ℕ} (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun r => (s r).demand = true)

def rows {B : ℕ} (s : V → Input V B) : V → Finset V :=
  GeneralCoveringRounding.normalize (fun r => (s r).candidates) (demands s)

noncomputable def vector {B : ℕ} (q : ℕ) (s : V → Input V B) (v : V) : ℝ :=
  (s v).numerator / (q : ℝ)

def cost {B : ℕ} (s : V → Input V B) (v : V) : ℝ := (s v).cost.val

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b B : ℕ} (ids : BitCode V b) (t q : ℕ) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((program ids B t q).runEncoded G s v).selected = true)

theorem rows_local {B : ℕ} (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) :
    ∀ r, rows s r ⊆ closed G r := by
  intro r
  by_cases hr : (s r).demand = true
  · simpa [rows, GeneralCoveringRounding.normalize, demands, hr] using hlocal r hr
  · simp [rows, GeneralCoveringRounding.normalize, demands, hr]

theorem rows_nonempty {B : ℕ} (s : V → Input V B)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    ∀ r ∈ demands s, (rows s r).Nonempty := by
  intro r hr
  simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using
    hrows r (Finset.mem_filter.mp hr).2

theorem output_eq {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (ht : 0 < t) (hq : 0 < q) (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    output G ids t q s =
      (Finset.univ.filter (fun v => 1 / (t : ℝ) ≤ vector q s v)) ∪
        ((demands s).filter (fun r => ∀ v ∈ rows s r, vector q s v < 1 / (t : ℝ))).image
          (CoveringRoundingCost.chosen (fun v => prepare t q (s v))) := by
  rw [output, output_image G ids t q s hlocal hrows, residual_eq t q ht hq s]
  apply congrArg₂ (fun A B : Finset V => A ∪ B)
  · ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vector]
    exact (threshold_iff t q (s v).numerator ht hq).symm
  · congr 1
    ext r
    by_cases hr : (s r).demand = true <;>
      simp [demands, rows, GeneralCoveringRounding.normalize, hr, vector]

theorem chosen_cost_le {B : ℕ} (t q : ℕ) (s : V → Input V B)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    ∀ r ∈ demands s, ∀ v ∈ rows s r,
      cost s (CoveringRoundingCost.chosen (fun v => prepare t q (s v)) r) ≤ cost s v := by
  intro r hr v hv
  have hrD := (Finset.mem_filter.mp hr).2
  have hc := (CoveringRoundingCost.chosen_spec (fun v => prepare t q (s v)) r (hrows r hrD)).2.2
  apply hc v
  simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hv

theorem closed_cost {b B : ℕ} (ids : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v) :
    (∑ v ∈ output G ids (2 * a + 1) q s, cost s v) ≤
      (2 * (a : ℝ) + 1) * ∑ v, cost s v * vector q s v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density
    (incidenceGraph G (rows s)) hden a le_rfl
  have hcoverN : ∀ r ∈ demands s, 1 ≤ ∑ v ∈ rows s r, vector q s v := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using
      hcover r (Finset.mem_filter.mp hr).2
  have h := CoveringRoundingCost.closed_cost_le G (rows s) (demands s) O ha
    (rows_local G s hlocal) (cost s) (vector q s)
    (fun v => Nat.cast_nonneg _) (fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rows_nonempty s hrows) hcoverN
    (CoveringRoundingCost.chosen (fun v => prepare (2 * a + 1) q (s v)))
    (chosen_cost_le (2 * a + 1) q s hrows)
  have he := output_eq G ids (2 * a + 1) q (by omega) hq s hlocal hrows
  rw [he]
  simpa only [GeneralCoveringRounding.large, GeneralCoveringRounding.residual,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

theorem open_cost {b B : ℕ} (ids : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hself : ∀ r, (s r).demand = true → r ∉ (s r).candidates)
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v) :
    (∑ v ∈ output G ids (2 * a) q s, cost s v) ≤
      (2 * (a : ℝ)) * ∑ v, cost s v * vector q s v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density
    (incidenceGraph G (rows s)) hden a le_rfl
  have hcoverN : ∀ r ∈ demands s, 1 ≤ ∑ v ∈ rows s r, vector q s v := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using
      hcover r (Finset.mem_filter.mp hr).2
  have hselfN : ∀ r ∈ demands s, r ∉ rows s r := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using
      hself r (Finset.mem_filter.mp hr).2
  have h := CoveringRoundingCost.open_cost_le G (rows s) (demands s) O ha
    (rows_local G s hlocal) (cost s) (vector q s)
    (fun v => Nat.cast_nonneg _) (fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rows_nonempty s hrows) hselfN hcoverN
    (CoveringRoundingCost.chosen (fun v => prepare (2 * a) q (s v)))
    (chosen_cost_le (2 * a) q s hrows)
  have he := output_eq G ids (2 * a) q (by omega) hq s hlocal hrows
  rw [he]
  simpa only [SelfExcludedRounding.large, SelfExcludedRounding.residual,
    Nat.cast_mul, Nat.cast_ofNat] using h

theorem output_admissible {b B : ℕ} (ids : BitCode V b) (t q : ℕ) (hq : 0 < q)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hsupport : ∀ v ∉ admissible (fun r => (s r).candidates) (demands s),
      (s v).numerator = 0) :
    output G ids t q s ⊆ admissible (fun r => (s r).candidates) (demands s) := by
  intro v hv
  rw [output, output_image G ids t q s hlocal hrows] at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · by_contra hn
    have hz := hsupport v hn
    have hs := (Finset.mem_filter.mp hv).2
    rw [hz, Nat.mul_zero] at hs
    omega
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hrD : (s r).demand = true := (Finset.mem_filter.mp hr).2.1
    have hc := (CoveringRoundingCost.chosen_spec (fun v => prepare t q (s v)) r (hrows r hrD)).2.1
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrD⟩, hc⟩

end Paper.CoveringThresholdCost

#print axioms Paper.CoveringThresholdCost.output_eq
#print axioms Paper.CoveringThresholdCost.closed_cost
#print axioms Paper.CoveringThresholdCost.open_cost
#print axioms Paper.CoveringThresholdCost.output_admissible
