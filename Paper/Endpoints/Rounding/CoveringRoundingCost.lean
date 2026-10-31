import Paper.Endpoints.Rounding.CoveringRoundingProtocol
import Paper.Endpoints.Rounding.SelfExcludedRounding

/-! Cost bounds are independent of the choice among equally cheap candidates. -/
namespace Paper.CoveringRoundingCost
open SevenFoundation OrientedNeighborhoods HallOrientation
open Paper.GeneralCoveringRounding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem union_image_cost_le (L T : Finset V) (f : V → V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) :
    (∑ v ∈ L ∪ T.image f, c v) ≤ (∑ v ∈ L, c v) + ∑ r ∈ T, c (f r) := by
  have hi := Finset.sum_image_le_of_nonneg (s := T) (f := c) (g := f)
    (fun v _ => hc v)
  have hu := Finset.sum_union_inter (s₁ := L) (s₂ := T.image f) (f := c)
  have hn : 0 ≤ ∑ v ∈ L ∩ T.image f, c v := Finset.sum_nonneg (fun v _ => hc v)
  linarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (ha : 1 ≤ a)
    (hlocal : ∀ r, C r ⊆ closed G r) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v)
    (f : V → V) (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v) :
    (∑ v ∈ GeneralCoveringRounding.large a x ∪ (GeneralCoveringRounding.residual C R a x).image f, c v) ≤
      (2 * (a : ℝ) + 1) * ∑ v, c v * x v := by
  classical
  let L := GeneralCoveringRounding.large a x
  let T := GeneralCoveringRounding.residual C R a x
  have hrequest : (∑ r ∈ T, c (f r)) ≤ ∑ r ∈ T, c (request C R hrows c r) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
    have hm : request C R hrows c r ∈ C r := by
      simpa [request, hrR] using cheapest_mem C c r (hrows r hrR)
    exact hf r hrR _ hm
  have hR := GeneralCoveringRounding.requests_cost_le G C R O ha hlocal c x hc hx hrows hcover
  have hL := GeneralCoveringRounding.large_cost_le a c x hc
  have hU := union_image_cost_le L T f c hc
  have hd : Disjoint L (Finset.univ \ L) :=
    Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp hw).2 hv)
  have he : L ∪ (Finset.univ \ L) = Finset.univ := by ext v; simp
  have hs : (∑ v ∈ L, c v * x v) + (∑ v ∈ Finset.univ \ L, c v * x v) =
      ∑ v, c v * x v := by rw [← Finset.sum_union hd, he]
  change (∑ v ∈ L ∪ T.image f, c v) ≤ _
  change (∑ r ∈ T, c (request C R hrows c r)) ≤
    (2 * (a : ℝ) + 1) * ∑ v ∈ Finset.univ \ L, c v * x v at hR
  change (∑ v ∈ L, c v) ≤ (2 * (a : ℝ) + 1) * ∑ v ∈ L, c v * x v at hL
  nlinarith only [hU, hrequest, hR, hL, hs]

theorem open_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (ha : 1 ≤ a)
    (hlocal : ∀ r, C r ⊆ closed G r) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v)
    (f : V → V) (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v) :
    (∑ v ∈ SelfExcludedRounding.large a x ∪ (SelfExcludedRounding.residual C R a x).image f, c v) ≤
      (2 * (a : ℝ)) * ∑ v, c v * x v := by
  classical
  let L := SelfExcludedRounding.large a x
  let T := SelfExcludedRounding.residual C R a x
  have hrequest : (∑ r ∈ T, c (f r)) ≤ ∑ r ∈ T, c (request C R hrows c r) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
    have hm : request C R hrows c r ∈ C r := by
      simpa [request, hrR] using cheapest_mem C c r (hrows r hrR)
    exact hf r hrR _ hm
  have hR := SelfExcludedRounding.requests_cost_le G C R O ha hlocal c x hc hx hrows hself hcover
  have hL := SelfExcludedRounding.large_cost_le a ha c x hc
  have hU := union_image_cost_le L T f c hc
  have hd : Disjoint L (Finset.univ \ L) :=
    Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp hw).2 hv)
  have he : L ∪ (Finset.univ \ L) = Finset.univ := by ext v; simp
  have hs : (∑ v ∈ L, c v * x v) + (∑ v ∈ Finset.univ \ L, c v * x v) =
      ∑ v, c v * x v := by rw [← Finset.sum_union hd, he]
  change (∑ v ∈ L ∪ T.image f, c v) ≤ _
  change (∑ r ∈ T, c (request C R hrows c r)) ≤
    (2 * (a : ℝ)) * ∑ v ∈ Finset.univ \ L, c v * x v at hR
  change (∑ v ∈ L, c v) ≤ (2 * (a : ℝ)) * ∑ v ∈ L, c v * x v at hL
  nlinarith only [hU, hrequest, hR, hL, hs]

end Paper.CoveringRoundingCost

namespace Paper.CoveringRoundingCost
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Protocol
open CoveringRoundingProtocol

def chosen {B : ℕ} (s : V → Input V B) (r : V) : V :=
  (choice (s r).candidates (fun v => (s v).cost)).getD r

theorem chosen_spec {B : ℕ} (s : V → Input V B) (r : V)
    (hr : (s r).candidates.Nonempty) :
    choice (s r).candidates (fun v => (s v).cost) = some (chosen s r) ∧
    chosen s r ∈ (s r).candidates ∧
    ∀ v ∈ (s r).candidates, ((s (chosen s r)).cost.val : ℝ) ≤ (s v).cost.val := by
  obtain ⟨u, hu, hm, hc⟩ := choice_spec (s r).candidates (fun v => (s v).cost) hr
  have he : chosen s r = u := by simp [chosen, hu]
  rw [he]
  refine ⟨hu, hm, ?_⟩
  intro v hv
  exact_mod_cast hc v hv

theorem requested_eq_image {B : ℕ} (s : V → Input V B) (W : Finset V)
    (hW : ∀ r ∈ W, (s r).demand = true)
    (hrows : ∀ r ∈ W, (s r).candidates.Nonempty) :
    GeneralCoveringRequests.requested (cheapestRows (fun v => normalized (s v))) W =
      W.image (chosen s) := by
  have hm (r : V) (hr : r ∈ W) :
      MaskedMinimum.minimum (cheapestRows (fun v => normalized (s v)) r) =
        some (chosen s r) := by
    have hs := (chosen_spec s r (hrows r hr)).1
    simp only [cheapestRows, normalized, hW r hr, ↓reduceIte]
    rw [hs]
    simp [MaskedMinimum.minimum]
  ext v
  rw [GeneralCoveringRequests.mem_requested, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, hr, Option.some.inj ((hm r hr).symm.trans hv)⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, hm r hr⟩

theorem normalized_output_image {b B : ℕ} (ids : BroadcastModel.BitCode V b)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty) :
    (Finset.univ.filter (fun v =>
      ((normalizedProgram ids B).runEncoded G s v).selected = true)) =
      (Finset.univ.filter (fun v => (s v).selected = true)) ∪
        (CoveringRoundingProtocol.residual s).image (chosen s) := by
  rw [normalized_output_eq G ids s hlocal]
  unfold GeneralCoveringRequests.selectedPlus
  rw [requested_eq_image s (CoveringRoundingProtocol.residual s)
    (fun r hr => (Finset.mem_filter.mp hr).2.1)
    (fun r hr => hrows r (Finset.mem_filter.mp hr).2.1)]

end Protocol
end Paper.CoveringRoundingCost

#print axioms Paper.CoveringRoundingCost.closed_cost_le
#print axioms Paper.CoveringRoundingCost.open_cost_le
#print axioms Paper.CoveringRoundingCost.chosen_spec
#print axioms Paper.CoveringRoundingCost.requested_eq_image
#print axioms Paper.CoveringRoundingCost.normalized_output_image
