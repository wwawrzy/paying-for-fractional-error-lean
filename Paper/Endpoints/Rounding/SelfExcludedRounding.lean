import Paper.Endpoints.Rounding.GeneralCoveringRounding

/-! The improved incoming-mass bound when demands cannot cover themselves. -/

namespace Paper.SelfExcludedRounding

open SevenFoundation OrientedNeighborhoods HallOrientation
open Paper.GeneralCoveringRounding
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Excluding the demand itself removes the extra nonincoming candidate. -/
theorem nonincoming_candidate_card_le (C : V → Finset V)
    (hclosed : ∀ r, C r ⊆ closed G r) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (r : V)
    (hself : r ∉ C r) :
    (C r \ incoming (incidenceGraph G C) O r).card ≤ a := by
  apply (Finset.card_le_card ?_).trans
    (outgoing_card_le (incidenceGraph G C) O r)
  intro v hv
  have hmem := GeneralCoveringRounding.nonincoming_candidate_subset G C hclosed O r hv
  rcases Finset.mem_insert.mp hmem with heq | hout
  · subst v
    exact False.elim (hself (Finset.mem_sdiff.mp hv).1)
  · exact hout

/-- At threshold `1 / (2a)`, at least half of the covering mass is incoming. -/
theorem incoming_mass_lower (C : V → Finset V) {a : ℕ}
    (ha : 1 ≤ a) (x : V → ℝ) (r : V)
    (hclosed : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a)
    (hself : r ∉ C r)
    (hsmall : ∀ v ∈ C r, x v < 1 / (2 * (a : ℝ)))
    (hcover : 1 ≤ ∑ v ∈ C r, x v) :
    (a : ℝ) / (2 * (a : ℝ)) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, x v := by
  classical
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  let A := C r ∩ incoming (incidenceGraph G C) O r
  have hsub : A ⊆ C r := Finset.inter_subset_left
  have hlow : (∑ v ∈ C r \ incoming (incidenceGraph G C) O r, x v) ≤
      (a : ℝ) / (2 * (a : ℝ)) := by
    calc
      _ ≤ ∑ _v ∈ C r \ incoming (incidenceGraph G C) O r,
          (1 / (2 * (a : ℝ))) :=
        Finset.sum_le_sum (fun v hv => le_of_lt (hsmall v (Finset.mem_sdiff.mp hv).1))
      _ = ((C r \ incoming (incidenceGraph G C) O r).card : ℝ) /
          (2 * (a : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right
        (by exact_mod_cast nonincoming_candidate_card_le G C hclosed O r hself)
        (by positivity)
  have hrest : C r \ A = C r \ incoming (incidenceGraph G C) O r := by
    ext v
    simp [A]
  have heq : (a : ℝ) / (2 * (a : ℝ)) = 1 / 2 := by
    field_simp
  have hsplit := Finset.sum_sdiff (s₁ := A) (s₂ := C r) (f := x) hsub
  rw [hrest] at hsplit
  change (∑ v ∈ C r \ incoming (incidenceGraph G C) O r, x v) +
    (∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, x v) = _ at hsplit
  linarith

noncomputable def large (a : ℕ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => 1 / (2 * (a : ℝ)) ≤ x v)

noncomputable def residual (C : V → Finset V) (R : Finset V)
    (a : ℕ) (x : V → ℝ) : Finset V := by
  classical
  exact R.filter (fun r => ∀ v ∈ C r, x v < 1 / (2 * (a : ℝ)))

noncomputable def selected (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (a : ℕ) (c x : V → ℝ) : Finset V := by
  classical
  exact large a x ∪ (residual C R a x).image (request C R hrows c)

theorem residual_small (C : V → Finset V) (R : Finset V) (a : ℕ)
    (x : V → ℝ) {r v : V} (hr : r ∈ residual C R a x) (hv : v ∈ C r) :
    x v < 1 / (2 * (a : ℝ)) :=
  (Finset.mem_filter.mp hr).2 v hv

theorem repair_charge (C : V → Finset V) (R : Finset V) {a : ℕ} (ha : 1 ≤ a)
    (hclosed : ∀ r, C r ⊆ closed G r)
    (O : Orientation (incidenceGraph G C) a) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    {r : V} (hr : r ∈ residual C R a x)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hself : r ∉ C r)
    (hcover : 1 ≤ ∑ v ∈ C r, x v) :
    (a : ℝ) * c (request C R hrows c r) ≤
      (2 * (a : ℝ)) *
        ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hrR : r ∈ R := (Finset.mem_filter.mp hr).1
  have hreq : request C R hrows c r = cheapest C c r (hrows r hrR) := by
    simp [request, hrR]
  rw [hreq]
  have hm := mul_le_mul_of_nonneg_left
    (incoming_mass_lower G C ha x r hclosed O hself
      (fun v hv => residual_small C R a x hr hv) hcover)
    (hc (cheapest C c r (hrows r hrR)))
  have hsum : c (cheapest C c r (hrows r hrR)) *
        (∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, x v) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_right
      (cheapest_cost_le C c r v (hrows r hrR) (Finset.mem_inter.mp hv).1) (hx v)
  have hpos : (0 : ℝ) < 2 * (a : ℝ) := by positivity
  have hdiv : (a : ℝ) * c (cheapest C c r (hrows r hrR)) /
        (2 * (a : ℝ)) ≤
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    calc
      _ = c (cheapest C c r (hrows r hrR)) *
          ((a : ℝ) / (2 * (a : ℝ))) := by ring
      _ ≤ _ := hm.trans hsum
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

theorem incoming_sum_le (C : V → Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (R : Finset V) (x f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ r ∈ residual C R a x,
      ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, f v) ≤
      (a : ℝ) * ∑ v ∈ Finset.univ \ large a x, f v := by
  classical
  rw [incoming_sum_identity]
  have hpoint : ∀ v,
      (((residual C R a x).filter
        (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r)).card : ℝ) * f v ≤
      if v ∈ Finset.univ \ large a x then (a : ℝ) * f v else 0 := by
    intro v
    by_cases hv : v ∈ large a x
    · have hempty : (residual C R a x).filter
        (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have hsmall := residual_small C R a x (Finset.mem_filter.mp hr).1
          (Finset.mem_filter.mp hr).2.1
        exact (not_lt_of_ge (Finset.mem_filter.mp hv).2) hsmall
      simp [hempty, hv]
    · have hsub : (residual C R a x).filter
        (fun r => v ∈ C r ∧ directs (incidenceGraph G C) O v r) ⊆
          outgoing (incidenceGraph G C) O v := by
        intro r hr
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
      have hcard := (Finset.card_le_card hsub).trans
        (outgoing_card_le (incidenceGraph G C) O v)
      have hvLow : v ∈ Finset.univ \ large a x :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
      simp [hvLow]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf v)
  calc
    _ ≤ ∑ v, if v ∈ Finset.univ \ large a x then (a : ℝ) * f v else 0 :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = _ := by
      have hset : (Finset.univ : Finset V).filter
          (fun v => v ∈ Finset.univ \ large a x) = Finset.univ \ large a x := by
        ext v
        simp
      rw [← Finset.sum_filter, hset, Finset.mul_sum]

omit [DecidableEq V] in
theorem large_cost_le (a : ℕ) (ha : 1 ≤ a) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    (∑ v ∈ large a x, c v) ≤
      (2 * (a : ℝ)) * ∑ v ∈ large a x, c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hpos : (0 : ℝ) < 2 * (a : ℝ) := by positivity
  have hxv := (div_le_iff₀ hpos).mp (Finset.mem_filter.mp hv).2
  have h := mul_le_mul_of_nonneg_left hxv (hc v)
  nlinarith only [h]

theorem requests_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (ha : 1 ≤ a)
    (hclosed : ∀ r, C r ⊆ closed G r) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    (∑ r ∈ residual C R a x, c (request C R hrows c r)) ≤
      (2 * (a : ℝ)) *
        ∑ v ∈ Finset.univ \ large a x, c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hp : (0 : ℝ) ≤ 2 * (a : ℝ) := by positivity
  have hcharges : (a : ℝ) *
      (∑ r ∈ residual C R a x, c (request C R hrows c r)) ≤
      (2 * (a : ℝ)) *
        ∑ r ∈ residual C R a x,
          ∑ v ∈ C r ∩ incoming (incidenceGraph G C) O r, c v * x v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    exact repair_charge G C R ha hclosed O c x hc hx hr hrows (hself r (Finset.mem_filter.mp hr).1)
      (hcover r (Finset.mem_filter.mp hr).1)
  have hinc := incoming_sum_le G C O R x (fun v => c v * x v)
    (fun v => mul_nonneg (hc v) (hx v))
  have hfinal : (a : ℝ) *
      (∑ r ∈ residual C R a x, c (request C R hrows c r)) ≤
      (a : ℝ) * ((2 * (a : ℝ)) *
        ∑ v ∈ Finset.univ \ large a x, c v * x v) := by
    calc
      _ ≤ _ := hcharges.trans (mul_le_mul_of_nonneg_left hinc hp)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hap).mp hfinal

theorem selected_covers (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (a : ℕ) (c x : V → ℝ)
    (_hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    ∀ r ∈ R, (selected C R hrows a c x ∩ C r).Nonempty := by
  classical
  intro r hr
  by_cases hlarge : ∃ v ∈ C r, v ∈ large a x
  · obtain ⟨v, hvr, hvL⟩ := hlarge
    exact ⟨v, Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ hvL, hvr⟩⟩
  · have hrT : r ∈ residual C R a x := by
      apply Finset.mem_filter.mpr
      refine ⟨hr, ?_⟩
      intro v hv
      by_contra hn
      have hvL : v ∈ large a x := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, le_of_not_gt hn⟩
      exact hlarge ⟨v, hv, hvL⟩
    have hreq : request C R hrows c r ∈ C r := by
      simp [request, hr]
      exact cheapest_mem C c r (hrows r hr)
    exact ⟨request C R hrows c r,
      Finset.mem_inter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨r, hrT, by simp [request, hr]⟩), hreq⟩⟩

theorem selected_subset_admissible (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (a : ℕ) (ha : 1 ≤ a) (c x : V → ℝ)
    (hsupport : ∀ v ∉ admissible C R, x v = 0) :
    selected C R hrows a c x ⊆ admissible C R := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvL | hvQ
  · by_contra hbad
    have hxv := (hsupport v hbad).symm
    have hthreshold : (0 : ℝ) < 1 / (2 * (a : ℝ)) := by positivity
    have hlarge := (Finset.mem_filter.mp hvL).2
    linarith
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hvQ
    have hrR := (Finset.mem_filter.mp hr).1
    have hvC : request C R hrows c r ∈ C r := by
      simp [request, hrR]
      exact cheapest_mem C c r (hrows r hrR)
    exact Finset.mem_biUnion.mpr ⟨r, hrR, hvC⟩

theorem selected_cost_le (C : V → Finset V) (R : Finset V) {a : ℕ}
    (O : Orientation (incidenceGraph G C) a) (ha : 1 ≤ a)
    (hclosed : ∀ r, C r ⊆ closed G r) (c x : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    (∑ v ∈ selected C R hrows a c x, c v) ≤
      (2 * (a : ℝ)) * ∑ v, c v * x v := by
  classical
  let T := residual C R a x
  let Q := T.image (request C R hrows c)
  have himage : (∑ v ∈ Q, c v) ≤ ∑ r ∈ T, c (request C R hrows c r) :=
    Finset.sum_image_le_of_nonneg (fun v _ => hc v)
  have hunion := Finset.sum_union_inter (s₁ := large a x) (s₂ := Q) (f := c)
  have hnonneg : 0 ≤ ∑ v ∈ large a x ∩ Q, c v :=
    Finset.sum_nonneg (fun v _ => hc v)
  have hL := large_cost_le a ha c x hc
  have hR := requests_cost_le G C R O ha hclosed c x hc hx hrows hself hcover
  have hdis : Disjoint (large a x) (Finset.univ \ large a x) := by
    exact Finset.disjoint_left.mpr (fun v hv hw => (Finset.mem_sdiff.mp hw).2 hv)
  have huniv : large a x ∪ (Finset.univ \ large a x) = Finset.univ := by
    ext v
    simp
  have htotal : (∑ v ∈ large a x, c v * x v) +
      (∑ v ∈ Finset.univ \ large a x, c v * x v) = ∑ v, c v * x v := by
    rw [← Finset.sum_union hdis, huniv]
  change (∑ v ∈ large a x ∪ Q, c v) ≤ _
  have hscale : (0 : ℝ) ≤ 2 * (a : ℝ) := by positivity
  have hcombined :
      (∑ v ∈ large a x, c v) + (∑ v ∈ Q, c v) ≤
        (2 * (a : ℝ)) *
          ((∑ v ∈ large a x, c v * x v) +
            (∑ v ∈ Finset.univ \ large a x, c v * x v)) := by
    nlinarith only [hL, himage, hR, htotal, hscale]
  have hU : (∑ v ∈ large a x ∪ Q, c v) ≤
      (∑ v ∈ large a x, c v) + (∑ v ∈ Q, c v) := by
    linarith [hunion, hnonneg]
  calc
    (∑ v ∈ large a x ∪ Q, c v) ≤
        (∑ v ∈ large a x, c v) + (∑ v ∈ Q, c v) := hU
    _ ≤ (2 * (a : ℝ)) *
        ((∑ v ∈ large a x, c v * x v) +
          (∑ v ∈ Finset.univ \ large a x, c v * x v)) := hcombined
    _ = (2 * (a : ℝ)) * ∑ v, c v * x v := by rw [htotal]

theorem exists_cover_rounding (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hclosed : ∀ r, C r ⊆ closed G r) {a : ℕ} (ha : 1 ≤ a)
    (hden : Incidence.InducedDensityBound (incidenceGraph G C) (a : ℝ))
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hsupport : ∀ v ∉ admissible C R, x v = 0)
    (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    ∃ D : Finset V,
      (D ⊆ admissible C R) ∧
      (∀ r ∈ R, (D ∩ C r).Nonempty) ∧
      (∑ v ∈ D, c v) ≤ (2 * (a : ℝ)) * ∑ v, c v * x v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density
    (incidenceGraph G C) hden a (le_rfl)
  exact ⟨selected C R hrows a c x,
    selected_subset_admissible C R hrows a ha c x hsupport,
    selected_covers C R hrows a c x hcover,
    selected_cost_le G C R O ha hclosed c x hc hx hrows hself hcover⟩

theorem exists_demand_cover_rounding (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hclosed : ∀ r ∈ R, C r ⊆ closed G r) {a : ℕ} (ha : 1 ≤ a)
    (hden : Incidence.InducedDensityBound
      (restricted_incidence_graph G C R) (a : ℝ))
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hsupport : ∀ v ∉ admissible C R, x v = 0)
    (hself : ∀ r ∈ R, r ∉ C r)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    ∃ D : Finset V,
      D ⊆ admissible C R ∧
      (∀ r ∈ R, (D ∩ C r).Nonempty) ∧
      (∑ v ∈ D, c v) ≤ (2 * (a : ℝ)) * ∑ v, c v * x v := by
  classical
  have hrowsN : ∀ r ∈ R, (GeneralCoveringRounding.normalize C R r).Nonempty := by
    intro r hr
    simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hrows r hr
  have hclosedN : ∀ r, GeneralCoveringRounding.normalize C R r ⊆ closed G r := by
    intro r
    by_cases hr : r ∈ R
    · simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hclosed r hr
    · simp only [GeneralCoveringRounding.normalize, if_neg hr]
      exact Finset.empty_subset _
  have hadm : admissible (GeneralCoveringRounding.normalize C R) R = admissible C R := by
    ext v
    simp only [admissible, Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, hv⟩
      exact ⟨r, hr, by simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hv⟩
    · rintro ⟨r, hr, hv⟩
      exact ⟨r, hr, by simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hv⟩
  have hsupportN : ∀ v ∉ admissible (GeneralCoveringRounding.normalize C R) R, x v = 0 := by
    simpa only [hadm] using hsupport
  have hcoverN : ∀ r ∈ R, 1 ≤ ∑ v ∈ GeneralCoveringRounding.normalize C R r, x v := by
    intro r hr
    simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hcover r hr
  have hselfN : ∀ r ∈ R, r ∉ GeneralCoveringRounding.normalize C R r := by
    intro r hr
    simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hself r hr
  obtain ⟨D, hD, hDC, hcost⟩ := exists_cover_rounding G
    (GeneralCoveringRounding.normalize C R) R hrowsN hclosedN ha hden c x hc hx hsupportN hselfN hcoverN
  refine ⟨D, ?_, ?_, hcost⟩
  · simpa only [hadm] using hD
  · intro r hr
    simpa only [GeneralCoveringRounding.normalize, if_pos hr] using hDC r hr

end Paper.SelfExcludedRounding

#print axioms Paper.SelfExcludedRounding.exists_cover_rounding
#print axioms Paper.SelfExcludedRounding.exists_demand_cover_rounding
