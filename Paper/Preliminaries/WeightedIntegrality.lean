import Paper.Preliminaries.OrientedNeighborhoods

/-! A weighted integral benchmark for partial domination, independent of the
fractional solver. Paper label: lem:integrality. -/
namespace Paper.WeightedIntegrality
attribute [local instance] Classical.propDecidable
open SevenFoundation OrientedNeighborhoods
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def large (a : ℕ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => 1 / (2 * (a : ℝ) + 1) ≤ x v)

noncomputable def remaining (R : Finset V) (a : ℕ) (x : V → ℝ) : Finset V :=
  R \ covered G (large a x)

noncomputable def cheapest (c : V → ℝ) (r : V) : V :=
  (Finset.exists_min_image (closed G r) c ⟨r, self_mem_closed G r⟩).choose

theorem cheapest_mem (c : V → ℝ) (r : V) : cheapest G c r ∈ closed G r :=
  (Finset.exists_min_image (closed G r) c ⟨r, self_mem_closed G r⟩).choose_spec.1

theorem cheapest_cost_le (c : V → ℝ) (r v : V) (hv : v ∈ closed G r) :
    c (cheapest G c r) ≤ c v :=
  (Finset.exists_min_image (closed G r) c ⟨r, self_mem_closed G r⟩).choose_spec.2 v hv

noncomputable def selection (R : Finset V) (a : ℕ) (c x : V → ℝ) : Finset V :=
  large a x ∪ (remaining G R a x).image (cheapest G c)

theorem remaining_closed_small (R : Finset V) (a : ℕ) (x : V → ℝ)
    {r v : V} (hr : r ∈ remaining G R a x) (hv : v ∈ closed G r) :
    x v < 1 / (2 * (a : ℝ) + 1) := by
  by_contra hn
  have hvl : v ∈ large a x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hn⟩
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_biUnion.mpr ⟨v, hvl, (closed_symm G v r).mp hv⟩)

theorem selection_covers (R : Finset V) (a : ℕ) (c x : V → ℝ) :
    ∀ r ∈ R, r ∈ covered G (selection G R a c x) := by
  intro r hr
  by_cases hlarge : r ∈ covered G (large a x)
  · exact covered_mono G Finset.subset_union_left hlarge
  · have hrR : r ∈ remaining G R a x := Finset.mem_sdiff.mpr ⟨hr, hlarge⟩
    exact Finset.mem_biUnion.mpr ⟨cheapest G c r,
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hrR, rfl⟩),
      (closed_symm G (cheapest G c r) r).mp (cheapest_mem G c r)⟩

theorem incoming_subset_closed {a : ℕ} (O : HallOrientation.Orientation G a) (r : V) :
    incoming G O r ⊆ closed G r := by
  intro v hv
  exact (mem_closed G v r).mpr (Or.inr (directs_adj G O (Finset.mem_filter.mp hv).2).symm)

theorem incoming_mass_lower (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (x : V → ℝ) {r : V} (hr : r ∈ remaining G R a x)
    (hcover : 1 ≤ ∑ v ∈ closed G r, x v) :
    (a : ℝ) / (2 * (a : ℝ) + 1) ≤ ∑ v ∈ incoming G O r, x v := by
  have hpos : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
  have hsmall : (∑ v ∈ closed G r \ incoming G O r, x v) ≤
      (a + 1 : ℕ) / (2 * (a : ℝ) + 1) := by
    calc
      _ ≤ ∑ _v ∈ closed G r \ incoming G O r, (1 / (2 * (a : ℝ) + 1)) :=
        Finset.sum_le_sum (fun v hv => le_of_lt
          (remaining_closed_small G R a x hr (Finset.mem_sdiff.mp hv).1))
      _ = ((closed G r \ incoming G O r).card : ℝ) / (2 * (a : ℝ) + 1) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast nonincoming_card_le G O r)
        (le_of_lt hpos)
  have hsplit := Finset.sum_sdiff (s₁ := incoming G O r) (s₂ := closed G r)
    (f := x) (incoming_subset_closed G O r)
  have heq : 1 - ((a + 1 : ℕ) : ℝ) / (2 * (a : ℝ) + 1) =
      (a : ℝ) / (2 * (a : ℝ) + 1) := by push_cast; field_simp; ring
  linarith

theorem repair_charge (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    {r : V} (hr : r ∈ remaining G R a x) (hcover : 1 ≤ ∑ v ∈ closed G r, x v) :
    (a : ℝ) * c (cheapest G c r) ≤
      (2 * (a : ℝ) + 1) * ∑ v ∈ incoming G O r, c v * x v := by
  have hm := mul_le_mul_of_nonneg_left (incoming_mass_lower G R O x hr hcover)
    (hc (cheapest G c r))
  have hsum : c (cheapest G c r) * (∑ v ∈ incoming G O r, x v) ≤
      ∑ v ∈ incoming G O r, c v * x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_right
      (cheapest_cost_le G c r v (incoming_subset_closed G O r hv)) (hx v)
  have hpos : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
  have hdiv : (a : ℝ) * c (cheapest G c r) / (2 * (a : ℝ) + 1) ≤
      ∑ v ∈ incoming G O r, c v * x v := by
    calc
      _ = c (cheapest G c r) * ((a : ℝ) / (2 * (a : ℝ) + 1)) := by ring
      _ ≤ _ := hm.trans hsum
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

/-- Incoming incidences are counted by outgoing loads on the other endpoint. -/
theorem incoming_sum_identity {a : ℕ} (O : HallOrientation.Orientation G a)
    (R : Finset V) (f : V → ℝ) :
    (∑ r ∈ R, ∑ v ∈ incoming G O r, f v) =
      ∑ v, ((R.filter (directs G O v)).card : ℝ) * f v := by
  classical
  simp only [incoming, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter]
  simp

/-- High coordinates cannot contribute to a remaining demand. -/
theorem incoming_sum_le {a : ℕ} (O : HallOrientation.Orientation G a)
    (R : Finset V) (x f : V → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ r ∈ remaining G R a x, ∑ v ∈ incoming G O r, f v) ≤
      (a : ℝ) * ∑ v ∈ (Finset.univ \ large a x), f v := by
  classical
  rw [incoming_sum_identity]
  have hpoint : ∀ v, (((remaining G R a x).filter (directs G O v)).card : ℝ) * f v ≤
      if v ∈ Finset.univ \ large a x then (a : ℝ) * f v else 0 := by
    intro v
    by_cases hv : v ∈ large a x
    · have hempty : (remaining G R a x).filter (directs G O v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have hrR := (Finset.mem_filter.mp hr).1
        have ha := directs_adj G O (Finset.mem_filter.mp hr).2
        exact (Finset.mem_sdiff.mp hrR).2 (Finset.mem_biUnion.mpr
          ⟨v, hv, (mem_closed G r v).mpr (Or.inr ha)⟩)
      simp [hempty, hv]
    · have hsub : (remaining G R a x).filter (directs G O v) ⊆ outgoing G O v := by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
      have hcard := (Finset.card_le_card hsub).trans (outgoing_card_le G O v)
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hv, not_false_eq_true, if_true]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf v)
  calc
    _ ≤ ∑ v, if v ∈ Finset.univ \ large a x then (a : ℝ) * f v else 0 :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = _ := by
      have hset : (Finset.univ : Finset V).filter (fun v => v ∈ Finset.univ \ large a x) =
          Finset.univ \ large a x := by ext v; simp
      rw [← Finset.sum_filter, hset, Finset.mul_sum]

/-- Threshold selections pay from the large-coordinate part of the vector. -/
theorem large_cost_le (a : ℕ) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    (∑ v ∈ large a x, c v) ≤ (2 * (a : ℝ) + 1) * ∑ v ∈ large a x, c v * x v := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hpos : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
  have hxv := (div_le_iff₀ hpos).mp (Finset.mem_filter.mp hv).2
  have h := mul_le_mul_of_nonneg_left hxv (hc v)
  nlinarith only [h]

theorem repairs_cost_le (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (ha : 1 ≤ a) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v) :
    (∑ r ∈ remaining G R a x, c (cheapest G c r)) ≤
      (2 * (a : ℝ) + 1) * ∑ v ∈ (Finset.univ \ large a x), c v * x v := by
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hp : (0 : ℝ) ≤ 2 * (a : ℝ) + 1 := by positivity
  have hcharges : (a : ℝ) * (∑ r ∈ remaining G R a x, c (cheapest G c r)) ≤
      (2 * (a : ℝ) + 1) * ∑ r ∈ remaining G R a x,
        ∑ v ∈ incoming G O r, c v * x v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun r hr => repair_charge G R O c x hc hx hr
      (hcover r (Finset.mem_sdiff.mp hr).1))
  have hinc := incoming_sum_le G O R x (fun v => c v * x v)
    (fun v => mul_nonneg (hc v) (hx v))
  have hfinal : (a : ℝ) * (∑ r ∈ remaining G R a x, c (cheapest G c r)) ≤
      (a : ℝ) * ((2 * (a : ℝ) + 1) * ∑ v ∈ (Finset.univ \ large a x), c v * x v) := by
    calc
      _ ≤ _ := hcharges.trans (mul_le_mul_of_nonneg_left hinc hp)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hap).mp hfinal

theorem selection_cost_le (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (ha : 1 ≤ a) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v) :
    (∑ v ∈ selection G R a c x, c v) ≤ (2 * (a : ℝ) + 1) * ∑ v, c v * x v := by
  classical
  have hi : (∑ v ∈ (remaining G R a x).image (cheapest G c), c v) ≤
      ∑ r ∈ remaining G R a x, c (cheapest G c r) :=
    Finset.sum_image_le_of_nonneg (fun v _ => hc v)
  have hu := Finset.sum_union_inter (s₁ := large a x)
    (s₂ := (remaining G R a x).image (cheapest G c)) (f := c)
  have hn : 0 ≤ ∑ v ∈ large a x ∩ (remaining G R a x).image (cheapest G c), c v :=
    Finset.sum_nonneg (fun v _ => hc v)
  have hL := large_cost_le a c x hc
  have hR := repairs_cost_le G R O ha c x hc hx hcover
  have hs := Finset.sum_sdiff (s₁ := large a x) (s₂ := Finset.univ)
    (f := fun v => c v * x v) (Finset.subset_univ _)
  change (∑ v ∈ large a x ∪ (remaining G R a x).image (cheapest G c), c v) ≤ _
  nlinarith only [hi, hu, hn, hL, hR, hs]

/-- The integral cover is built from the actual graph and a feasible vector.
No fractional solver or assumed integral optimum estimate is used. -/
theorem exists_integral_cover (R : Finset V) (a : ℕ) (ha : 1 ≤ a)
    (hden : ∀ S : Finset V, G.inducedEdgeCount S ≤ a * S.card)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v) :
    ∃ D : Finset V, (∀ r ∈ R, r ∈ covered G D) ∧
      (∑ v ∈ D, c v) ≤ (2 * (a : ℝ) + 1) * ∑ v, c v * x v := by
  obtain ⟨O⟩ := HallOrientation.exists_orientation G a hden
  exact ⟨selection G R a c x, selection_covers G R a c x,
    selection_cost_le G R O ha c x hc hx hcover⟩

end Paper.WeightedIntegrality
