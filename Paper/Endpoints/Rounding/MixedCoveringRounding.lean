import Paper.Endpoints.Rounding.CoveringRoundingCost

/-! One candidate-dependent threshold gives the general bound and its
self-excluded improvement, without a global choice of algorithm. -/

namespace Paper.MixedCoveringRounding

open SevenFoundation OrientedNeighborhoods HallOrientation
open GeneralCoveringRounding
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every candidate in a self-covering demand's row uses the smaller threshold. -/
def flagged (C : V → Finset V) (R : Finset V) (v : V) : Prop :=
  ∃ r ∈ R, r ∈ C r ∧ v ∈ C r

noncomputable def scale (C : V → Finset V) (R : Finset V) (a : ℕ) (v : V) : ℝ :=
  if flagged C R v then 2 * (a : ℝ) + 1 else 2 * (a : ℝ)

noncomputable def large (C : V → Finset V) (R : Finset V)
    (a : ℕ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => 1 / scale C R a v ≤ x v)

noncomputable def residual (C : V → Finset V) (R : Finset V)
    (a : ℕ) (x : V → ℝ) : Finset V :=
  R.filter (fun r => ∀ v ∈ C r, v ∉ large C R a x)

noncomputable def selected (C : V → Finset V) (R : Finset V)
    (a : ℕ) (x : V → ℝ) (f : V → V) : Finset V :=
  large C R a x ∪ (residual C R a x).image f

omit [Fintype V] [DecidableEq V] in
theorem scale_bounds (C : V → Finset V) (R : Finset V) (a : ℕ) (v : V) :
    2 * (a : ℝ) ≤ scale C R a v ∧ scale C R a v ≤ 2 * (a : ℝ) + 1 := by
  unfold scale
  split_ifs <;> constructor <;> linarith

theorem residual_small (C : V → Finset V) (R : Finset V) (a : ℕ)
    (x : V → ℝ) {r v : V} (hr : r ∈ residual C R a x) (hv : v ∈ C r) :
    x v < 1 / scale C R a v := by
  have hn := (Finset.mem_filter.mp hr).2 v hv
  exact lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem incoming_mass_lower (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (x : V → ℝ) {r : V} (hr : r ∈ residual C R a x)
    (hlocal : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a)
    (hcover : 1 ≤ ∑ v ∈ C r, x v) :
    (a : ℝ) / (2 * (a : ℝ) + 1) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hrR := (Finset.mem_filter.mp hr).1
  by_cases hself : r ∈ C r
  · apply GeneralCoveringRounding.incoming_mass_lower G C R a x
      (Finset.mem_filter.mpr ⟨hrR, ?_⟩) hlocal O hcover
    intro v hv
    have hf : flagged C R v := ⟨r, hrR, hself, hv⟩
    simpa only [scale, if_pos hf] using residual_small C R a x hr hv
  · have hm := SelfExcludedRounding.incoming_mass_lower G C ha x r hlocal O hself
      (fun v hv => (residual_small C R a x hr hv).trans_le
        (one_div_le_one_div_of_le (by positivity) (scale_bounds C R a v).1)) hcover
    have hs : (a : ℝ) / (2 * (a : ℝ) + 1) ≤ (a : ℝ) / (2 * (a : ℝ)) :=
      div_le_div_of_nonneg_left (le_of_lt hap) (by positivity) (by linarith)
    exact hs.trans hm

/-- Reuse the exact outgoing-multiplicity identity for the mixed residual set. -/
theorem incoming_sum_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (x w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) :
    (∑ r ∈ residual C R a x,
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, w v) ≤
      (a : ℝ) * ∑ v ∈ Finset.univ \ large C R a x, w v := by
  rw [GeneralCoveringRounding.incoming_sum_identity]
  have hp (v : V) :
      (((residual C R a x).filter
        (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r)).card : ℝ) * w v ≤
      if v ∈ Finset.univ \ large C R a x then (a : ℝ) * w v else 0 := by
    by_cases hv : v ∈ large C R a x
    · have he : (residual C R a x).filter
          (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2 v
          (Finset.mem_filter.mp hr).2.1 hv
      simp [he, hv]
    · have hsub : (residual C R a x).filter
          (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r) ⊆
          outgoing (incidenceGraph G C) O v := by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
      have hcard := (Finset.card_le_card hsub).trans
        (outgoing_card_le (incidenceGraph G C) O v)
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hv,
        not_false_eq_true, if_true]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hw v)
  calc
    _ ≤ ∑ v, if v ∈ Finset.univ \ large C R a x then (a : ℝ) * w v else 0 :=
      Finset.sum_le_sum (fun v _ => hp v)
    _ = _ := by
      have he : (Finset.univ : Finset V).filter
          (fun v => v ∈ Finset.univ \ large C R a x) =
          Finset.univ \ large C R a x := by ext v; simp
      rw [← Finset.sum_filter, he, Finset.mul_sum]

theorem repair_charge (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (hlocal : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) (f : V → V)
    (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v)
    {r : V} (hr : r ∈ residual C R a x)
    (hcover : 1 ≤ ∑ v ∈ C r, x v) :
    (a : ℝ) * c (f r) ≤ (2 * (a : ℝ) + 1) *
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
  have hm := mul_le_mul_of_nonneg_left
    (incoming_mass_lower G C R ha x hr hlocal O hcover) (hc (f r))
  have hs : c (f r) * (∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, x v) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right
      (hf r (Finset.mem_filter.mp hr).1 v (Finset.mem_inter.mp hv).1) (hx v))
  have hd : (a : ℝ) * c (f r) / (2 * (a : ℝ) + 1) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    calc
      _ = c (f r) * ((a : ℝ) / (2 * (a : ℝ) + 1)) := by ring
      _ ≤ _ := hm.trans hs
  simpa only [mul_comm] using (div_le_iff₀ (by positivity :
    (0 : ℝ) < 2 * (a : ℝ) + 1)).mp hd

theorem requests_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (hlocal : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) (f : V → V)
    (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    (∑ r ∈ residual C R a x, c (f r)) ≤ (2 * (a : ℝ) + 1) *
      ∑ v ∈ Finset.univ \ large C R a x, c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hs : (a : ℝ) * (∑ r ∈ residual C R a x, c (f r)) ≤
      (2 * (a : ℝ) + 1) * ∑ r ∈ residual C R a x,
        ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun r hr => repair_charge G C R ha hlocal O c x hc hx f hf
      hr (hcover r (Finset.mem_filter.mp hr).1))
  have hi := incoming_sum_le G C R O x (fun v => c v * x v)
    (fun v => mul_nonneg (hc v) (hx v))
  apply (mul_le_mul_iff_right₀ hap).mp
  calc
    _ ≤ _ := hs.trans (mul_le_mul_of_nonneg_left hi (by positivity))
    _ = _ := by ring

theorem large_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    (∑ v ∈ large C R a x, c v) ≤
      (2 * (a : ℝ) + 1) * ∑ v ∈ large C R a x, c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hs := scale_bounds C R a v
  have hp : 0 < scale C R a v := lt_of_lt_of_le (by positivity) hs.1
  have hm := mul_le_mul_of_nonneg_left
    ((div_le_iff₀ hp).mp (Finset.mem_filter.mp hv).2) (hc v)
  have hxv : 0 ≤ x v := le_trans (by positivity : (0 : ℝ) ≤ 1 / scale C R a v)
    (Finset.mem_filter.mp hv).2
  calc
    c v ≤ scale C R a v * (c v * x v) := by nlinarith only [hm]
    _ ≤ (2 * (a : ℝ) + 1) * (c v * x v) :=
      mul_le_mul_of_nonneg_right hs.2 (mul_nonneg (hc v) hxv)

/-- Arbitrary cheapest tie-breaking gives the same bound for the one mixed rule. -/
theorem cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (hlocal : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) (f : V → V)
    (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    (∑ v ∈ selected C R a x f, c v) ≤ (2 * (a : ℝ) + 1) * ∑ v, c v * x v := by
  have hU := CoveringRoundingCost.union_image_cost_le
    (large C R a x) (residual C R a x) f c hc
  have hL := large_cost_le C R ha c x hc
  have hR := requests_cost_le G C R ha hlocal O c x hc hx f hf hcover
  have hs := Finset.sum_sdiff (s₁ := large C R a x) (s₂ := Finset.univ)
    (f := fun v => c v * x v) (Finset.subset_univ _)
  unfold selected
  nlinarith only [hU, hL, hR, hs]

omit [Fintype V] [DecidableEq V] in
theorem no_self_scale (C : V → Finset V) (R : Finset V) (a : ℕ)
    (hself : ∀ r ∈ R, r ∉ C r) (v : V) : scale C R a v = 2 * (a : ℝ) := by
  have hn : ¬ flagged C R v := by
    rintro ⟨r, hr, hs, _⟩
    exact hself r hr hs
  exact if_neg hn

/-- The same selection, under global self-exclusion, has factor `2a`. -/
theorem no_self_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (ha : 1 ≤ a) (hlocal : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v)
    (f : V → V) (hf : ∀ r ∈ R, ∀ v ∈ C r, c (f r) ≤ c v) :
    (∑ v ∈ selected C R a x f, c v) ≤ (2 * (a : ℝ)) * ∑ v, c v * x v := by
  have hL : large C R a x = SelfExcludedRounding.large a x := by
    ext v
    simp only [large, SelfExcludedRounding.large, Finset.mem_filter,
      no_self_scale C R a hself]
  have hT : residual C R a x = SelfExcludedRounding.residual C R a x := by
    ext r
    simp only [residual, SelfExcludedRounding.residual, Finset.mem_filter, hL,
      SelfExcludedRounding.large, Finset.mem_univ, true_and, not_le]
  simpa only [selected, hL, hT] using
    CoveringRoundingCost.open_cost_le G C R O ha hlocal c x hc hx hrows hself hcover f hf

end Paper.MixedCoveringRounding

#print axioms Paper.MixedCoveringRounding.incoming_mass_lower
#print axioms Paper.MixedCoveringRounding.incoming_sum_le
#print axioms Paper.MixedCoveringRounding.repair_charge
#print axioms Paper.MixedCoveringRounding.requests_cost_le
#print axioms Paper.MixedCoveringRounding.large_cost_le
#print axioms Paper.MixedCoveringRounding.cost_le
#print axioms Paper.MixedCoveringRounding.no_self_cost_le
