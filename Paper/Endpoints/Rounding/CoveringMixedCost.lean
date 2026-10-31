import Paper.Endpoints.Rounding.CoveringMixedOutput

/-! Bounds for the same executed mixed-threshold output in both cases. -/
namespace Paper.CoveringMixedCost
open BroadcastModel SevenFoundation GeneralCoveringRounding
open CoveringMixedOutput
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b B : ℕ} (I : BitCode V b) (a q : ℕ) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((CoveringThresholdFlags.roundedProgram I B a q).runEncoded G s v).selected = true)

def cost {B : ℕ} (s : V → Input V B) (v : V) : ℝ := (s v).cost.val

theorem output_eq {b B : ℕ} (I : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    output G I a q s = MixedCoveringRounding.selected (rows s) (demands s) a (vector q s)
      (CoveringRoundingCost.chosen (prepared G a q s)) := by
  unfold output
  rw [CoveringThresholdFlags.rounded_run]
  change (Finset.univ.filter (fun v =>
    ((CoveringRoundingProtocol.normalizedProgram I B).runEncoded G (prepared G a q s) v).selected = true)) = _
  rw [CoveringRoundingCost.normalized_output_image G I (prepared G a q s) hlocal hrows]
  rw [large_eq G a q ha hq s hinc hlocal, residual_eq G a q ha hq s hinc hlocal]
  rfl

theorem rows_local {B : ℕ} (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) :
    ∀ r, rows s r ⊆ closed G r := by
  intro r
  by_cases hd : (s r).demand = true
  · simpa [rows, demands, GeneralCoveringRounding.normalize, hd] using hlocal r hd
  · simp [rows, demands, GeneralCoveringRounding.normalize, hd]

theorem chosen_cost_le {B : ℕ} (a q : ℕ) (s : V → Input V B)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    ∀ r ∈ demands s, ∀ v ∈ rows s r,
      cost s (CoveringRoundingCost.chosen (prepared G a q s) r) ≤ cost s v := by
  intro r hr v hv
  have hd := (Finset.mem_filter.mp hr).2
  have hc := (CoveringRoundingCost.chosen_spec (prepared G a q s) r (hrows r hd)).2.2
  apply hc v
  simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hv

theorem closed_cost {b B : ℕ} (I : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v) :
    (∑ v ∈ output G I a q s, cost s v) ≤
      (2 * (a : ℝ) + 1) * ∑ v, cost s v * vector q s v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density
    (incidenceGraph G (rows s)) hden a le_rfl
  have hcoverN : ∀ r ∈ demands s, 1 ≤ ∑ v ∈ rows s r, vector q s v := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hcover r (Finset.mem_filter.mp hr).2
  rw [output_eq G I a q ha hq s hinc hlocal hrows]
  exact MixedCoveringRounding.cost_le G (rows s) (demands s) ha (rows_local G s hlocal)
    O (cost s) (vector q s) (fun v => Nat.cast_nonneg _)
    (fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (CoveringRoundingCost.chosen (prepared G a q s)) (chosen_cost_le G a q s hrows) hcoverN

theorem open_cost {b B : ℕ} (I : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hself : ∀ r, (s r).demand = true → r ∉ (s r).candidates)
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v) :
    (∑ v ∈ output G I a q s, cost s v) ≤
      (2 * (a : ℝ)) * ∑ v, cost s v * vector q s v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density
    (incidenceGraph G (rows s)) hden a le_rfl
  have hcoverN : ∀ r ∈ demands s, 1 ≤ ∑ v ∈ rows s r, vector q s v := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hcover r (Finset.mem_filter.mp hr).2
  have hrowsN : ∀ r ∈ demands s, (rows s r).Nonempty := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hrows r (Finset.mem_filter.mp hr).2
  have hselfN : ∀ r ∈ demands s, r ∉ rows s r := by
    intro r hr
    simpa only [rows, GeneralCoveringRounding.normalize, if_pos hr] using hself r (Finset.mem_filter.mp hr).2
  rw [output_eq G I a q ha hq s hinc hlocal hrows]
  exact MixedCoveringRounding.no_self_cost_le G (rows s) (demands s) ha (rows_local G s hlocal)
    O (cost s) (vector q s) (fun v => Nat.cast_nonneg _)
    (fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hrowsN hselfN hcoverN
    (CoveringRoundingCost.chosen (prepared G a q s)) (chosen_cost_le G a q s hrows)

end Paper.CoveringMixedCost

#print axioms Paper.CoveringMixedCost.output_eq
#print axioms Paper.CoveringMixedCost.closed_cost
#print axioms Paper.CoveringMixedCost.open_cost
