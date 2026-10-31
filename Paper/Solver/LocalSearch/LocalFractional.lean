import Paper.Solver.LocalSearch.SearchSize

/-! Bounded finite local optimization and its fractional approximation guarantee.
This is the mathematical search; its CONGEST_BC execution is still separate. -/
namespace Paper.LocalFractional
attribute [local instance] Classical.propDecidable
open SevenFoundation FiniteSearch
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def demand (R : Finset V) (q : ℕ) (r : V) : ℕ := if r ∈ R then q else 0

noncomputable def best (t : ℝ) (c : V → ℝ) (M : ℕ) (b : V → ℕ) : Option (V → ℕ) :=
  if h : (ExactSearch.search G t c M b).Nonempty then
    some (Finset.exists_min_image (ExactSearch.search G t c M b) (integerCost c) h).choose
  else none

theorem best_exists_of_valid (t : ℝ) (ht : 1 ≤ t) (c : V → ℝ) (M : ℕ) (b : V → ℕ)
    (p : V → ℕ) (hp : valid G M b p) :
    ∃ p', best G t c M b = some p' ∧ valid G M b p' ∧ integerCost c p' ≤ integerCost c p := by
  obtain ⟨z, hz, hzcost⟩ := ExactSearch.search_complete G t ht c M b p hp
  have hn : (ExactSearch.search G t c M b).Nonempty := ⟨z, hz⟩
  let p' := (Finset.exists_min_image (ExactSearch.search G t c M b) (integerCost c) hn).choose
  have hp' := (Finset.exists_min_image (ExactSearch.search G t c M b) (integerCost c) hn).choose_spec
  refine ⟨p', ?_, ExactSearch.search_sound G t c M b hp'.1, (hp'.2 z hz).trans hzcost⟩
  simp only [best, dif_pos hn]
  rfl

noncomputable def vector (q : ℕ) (p : V → ℕ) (v : V) : ℝ := (p v : ℝ) / q

theorem vector_nonneg (q : ℕ) (p : V → ℕ) (v : V) : 0 ≤ vector q p v := by
  unfold vector
  positivity

theorem vector_covers (R : Finset V) (q : ℕ) (hq : 1 ≤ q) (M : ℕ) (p : V → ℕ)
    (hp : valid G M (demand R q) p) : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, vector q p v := by
  intro r hr
  have h := hp.2 r
  simp only [demand, if_pos hr] at h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  unfold vector
  rw [← Finset.sum_div]
  apply (le_div_iff₀ hqpos).mpr
  simpa only [one_mul] using (show (q : ℝ) ≤ ∑ v ∈ closed G r, (p v : ℝ) by exact_mod_cast h)

theorem vector_cost (c : V → ℝ) (q : ℕ) (p : V → ℕ) :
    (∑ v, c v * vector q p v) = integerCost c p / q := by
  simp only [vector, integerCost, mul_div_assoc, Finset.sum_div]

/-- Search budget and common denominator depend only on fixed parameters.
The chosen result is compared against every supplied feasible benchmark vector. -/
theorem best_approximation (R : Finset V) (t : ℝ) (ht : 1 ≤ t)
    {a : ℕ} (O : HallOrientation.Orientation G a) (ha : 1 ≤ a)
    (q : ℕ) (hq : 1 ≤ q) (c x : V → ℝ) (hc : ∀ v, 1 ≤ c v)
    (hx : ∀ v, 0 ≤ x v) (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v)
    (K : ℝ) (hK : (∑ v, c v * x v) ≤ K) :
    ∃ p : V → ℕ,
      best G t c ⌈(q + 2 * (a : ℝ)) * K⌉₊ (demand R q) = some p ∧
      (∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, vector q p v) ∧
      (∑ v, c v * vector q p v) ≤ (1 + 2 * (a : ℝ) / q) * ∑ v, c v * x v := by
  classical
  obtain ⟨m, hmcover, hmcost⟩ := WeightedCertificate.exists_certificate G R O ha q c x hx hcover
  let M := ⌈(q + 2 * (a : ℝ)) * K⌉₊
  have hcoef : 0 ≤ q + 2 * (a : ℝ) := by positivity
  have hcopies := WeightedCertificate.copies_le_cost c hc m
  have hbound : (∑ v, (m v : ℝ)) ≤ M :=
    hcopies.trans (hmcost.trans ((mul_le_mul_of_nonneg_left hK hcoef).trans (Nat.le_ceil _)))
  have hvalid : valid G M (demand R q) m := by
    refine ⟨by exact_mod_cast hbound, ?_⟩
    intro r
    by_cases hr : r ∈ R
    · simpa only [demand, if_pos hr] using hmcover r hr
    · simp only [demand, if_neg hr, zero_le]
  obtain ⟨p, hbest, hp, hpcost⟩ := best_exists_of_valid G t ht c M (demand R q) m hvalid
  refine ⟨p, hbest, vector_covers G R q hq M p hp, ?_⟩
  rw [vector_cost]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h := div_le_div_of_nonneg_right (hpcost.trans hmcost) hqpos.le
  have heq : ((q : ℝ) + 2 * (a : ℝ)) * (∑ v, c v * x v) / q =
      (1 + 2 * (a : ℝ) / q) * ∑ v, c v * x v := by field_simp <;> ring
  exact h.trans_eq heq
end Paper.LocalFractional
