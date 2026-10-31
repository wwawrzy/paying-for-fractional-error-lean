import Paper.Endpoints.Rounding.CoveringThresholdFlags
import Paper.Endpoints.Rounding.MixedCoveringRounding

/-! Match the actual four-round mixed-threshold program to its cost analysis. -/
namespace Paper.CoveringMixedOutput
open BroadcastModel SevenFoundation
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

abbrev Input := CoveringThresholdFlags.Input

def demands {B : ℕ} (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun r => (s r).demand = true)

def rows {B : ℕ} (s : V → Input V B) : V → Finset V :=
  GeneralCoveringRounding.normalize (fun r => (s r).candidates) (demands s)

noncomputable def vector {B : ℕ} (q : ℕ) (s : V → Input V B) (v : V) : ℝ :=
  (s v).numerator / (q : ℝ)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def prepared {B : ℕ} (a q : ℕ) (s : V → Input V B) :
    V → CoveringRoundingProtocol.Input V B := fun v =>
  CoveringThresholdFlags.finish a q (closed G v ∩ CoveringThresholdFlags.selfDemands s) (s v)

theorem flagged_iff {B : ℕ} (s : V → Input V B) (v : V) :
    MixedCoveringRounding.flagged (rows s) (demands s) v ↔
      ∃ r, (s r).demand = true ∧ r ∈ (s r).candidates ∧ v ∈ (s r).candidates := by
  simp only [MixedCoveringRounding.flagged, rows, GeneralCoveringRounding.normalize,
    demands, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hd, hs, hv⟩
    exact ⟨r, hd, by simpa [hd] using hs, by simpa [hd] using hv⟩
  · rintro ⟨r, hd, hs, hv⟩
    exact ⟨r, hd, by simpa [hd] using hs, by simpa [hd] using hv⟩

theorem selected_iff {B : ℕ} (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) (v : V) :
    (prepared G a q s v).selected = true ↔
      1 / MixedCoveringRounding.scale (rows s) (demands s) a v ≤ vector q s v := by
  have h := CoveringThresholdFlags.selected_iff G a q s hinc hlocal v
  rw [CoveringThresholdFlags.run] at h
  change (prepared G a q s v).selected = true ↔ _ at h
  by_cases hf : MixedCoveringRounding.flagged (rows s) (demands s) v
  · have he := (flagged_iff s v).mp hf
    simp only [if_pos he] at h
    exact h.trans (by simpa [MixedCoveringRounding.scale, hf, vector] using
      (CoveringThresholdInput.threshold_iff (2 * a + 1) q (s v).numerator (by omega) hq).symm)
  · have he := mt (flagged_iff s v).mpr hf
    simp only [if_neg he] at h
    exact h.trans (by simpa [MixedCoveringRounding.scale, hf, vector] using
      (CoveringThresholdInput.threshold_iff (2 * a) q (s v).numerator (by omega) hq).symm)

theorem large_eq {B : ℕ} (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) :
    Finset.univ.filter (fun v => (prepared G a q s v).selected = true) =
      MixedCoveringRounding.large (rows s) (demands s) a (vector q s) := by
  ext v
  simp only [MixedCoveringRounding.large, Finset.mem_filter, Finset.mem_univ, true_and]
  exact selected_iff G a q ha hq s hinc hlocal v

theorem residual_eq {B : ℕ} (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) :
    CoveringRoundingProtocol.residual (prepared G a q s) =
      MixedCoveringRounding.residual (rows s) (demands s) a (vector q s) := by
  unfold CoveringRoundingProtocol.residual
  rw [large_eq G a q ha hq s hinc hlocal]
  ext r
  by_cases hd : (s r).demand = true
  · simp [MixedCoveringRounding.residual, rows, demands, GeneralCoveringRounding.normalize,
      prepared, CoveringThresholdFlags.finish, hd, Finset.eq_empty_iff_forall_notMem]
  · simp [MixedCoveringRounding.residual, demands, prepared, CoveringThresholdFlags.finish, hd]

end Paper.CoveringMixedOutput

#print axioms Paper.CoveringMixedOutput.flagged_iff
#print axioms Paper.CoveringMixedOutput.selected_iff
#print axioms Paper.CoveringMixedOutput.large_eq
#print axioms Paper.CoveringMixedOutput.residual_eq
