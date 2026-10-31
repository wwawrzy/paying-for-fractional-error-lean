import Paper.Endpoints.Rounding.CoveringMixedCost

/-! Feasibility and support of the executed mixed-threshold cover. -/
namespace Paper.CoveringMixedFeasible
open BroadcastModel SevenFoundation GeneralCoveringRounding
open CoveringMixedOutput CoveringMixedCost
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem covers {b B : ℕ} (I : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (r : V) (hr : (s r).demand = true) :
    ∃ v ∈ (s r).candidates, v ∈ output G I a q s := by
  rw [CoveringMixedCost.output_eq G I a q ha hq s hinc hlocal hrows]
  have hrR : r ∈ demands s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  by_cases hh : ∃ v ∈ (s r).candidates,
      v ∈ MixedCoveringRounding.large (rows s) (demands s) a (vector q s)
  · obtain ⟨v, hv, hm⟩ := hh
    exact ⟨v, hv, Finset.mem_union_left _ hm⟩
  · have hrT : r ∈ MixedCoveringRounding.residual (rows s) (demands s) a (vector q s) := by
      refine Finset.mem_filter.mpr ⟨hrR, ?_⟩
      intro v hv hm
      have hvC : v ∈ (s r).candidates := by
        simpa only [rows, GeneralCoveringRounding.normalize, if_pos hrR] using hv
      exact hh ⟨v, hvC, hm⟩
    let f := CoveringRoundingCost.chosen (prepared G a q s)
    have hc : f r ∈ (s r).candidates :=
      (CoveringRoundingCost.chosen_spec (prepared G a q s) r (hrows r hr)).2.1
    exact ⟨f r, hc, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hrT, rfl⟩)⟩

theorem admissible_output {b B : ℕ} (I : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hsupport : ∀ v ∉ admissible (fun r => (s r).candidates) (demands s), vector q s v = 0) :
    output G I a q s ⊆ admissible (fun r => (s r).candidates) (demands s) := by
  intro v hv
  rw [CoveringMixedCost.output_eq G I a q ha hq s hinc hlocal hrows] at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · by_contra hn
    have hz := hsupport v hn
    have hs := (Finset.mem_filter.mp hv).2
    rw [hz] at hs
    have hb := (MixedCoveringRounding.scale_bounds (rows s) (demands s) a v).1
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hp : 0 < MixedCoveringRounding.scale (rows s) (demands s) a v := by linarith
    exact (not_le_of_gt (one_div_pos.mpr hp)) hs
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hrR := (Finset.mem_filter.mp hr).1
    have hd := (Finset.mem_filter.mp hrR).2
    have hc := (CoveringRoundingCost.chosen_spec (prepared G a q s) r (hrows r hd)).2.1
    exact Finset.mem_biUnion.mpr ⟨r, hrR, hc⟩

end Paper.CoveringMixedFeasible

#print axioms Paper.CoveringMixedFeasible.covers
#print axioms Paper.CoveringMixedFeasible.admissible_output
