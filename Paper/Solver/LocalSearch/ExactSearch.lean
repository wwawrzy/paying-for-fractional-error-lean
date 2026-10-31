import Paper.Solver.LocalSearch.FiniteSearch

/-! Actual recursive exact search over bounded multicover certificates.
The distributed execution schedule remains a separate obligation. -/
namespace Paper.ExactSearch
attribute [local instance] Classical.propDecidable
open SevenFoundation FiniteSearch
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def addOne (v : V) (p : V → ℕ) (u : V) : ℕ := p u + if u = v then 1 else 0

noncomputable def eraseOne (v : V) (p : V → ℕ) (u : V) : ℕ := p u - if u = v then 1 else 0

noncomputable def reduce (b : V → ℕ) (v r : V) : ℕ := b r - if v ∈ closed G r then 1 else 0

theorem sum_addOne (T : Finset V) (v : V) (p : V → ℕ) :
    (∑ u ∈ T, addOne v p u) = (∑ u ∈ T, p u) + if v ∈ T then 1 else 0 := by
  simp only [addOne, Finset.sum_add_distrib]
  simp

theorem cost_addOne (c : V → ℝ) (v : V) (p : V → ℕ) :
    integerCost c (addOne v p) = integerCost c p + c v := by
  unfold integerCost addOne
  simp only [Nat.cast_add, mul_add, Finset.sum_add_distrib, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  simp

theorem add_erase (v : V) (p : V → ℕ) (hp : 0 < p v) : addOne v (eraseOne v p) = p := by
  funext u
  by_cases hu : u = v
  · subst u
    simp only [addOne, eraseOne, ite_true]
    omega
  · simp only [addOne, eraseOne, if_neg hu, Nat.sub_zero, add_zero]

theorem covers_addOne_iff (b : V → ℕ) (v : V) (p : V → ℕ) :
    covers G b (addOne v p) ↔ covers G (reduce G b v) p := by
  unfold covers reduce
  simp_rw [sum_addOne, Nat.sub_le_iff_le_add]

theorem valid_addOne (b : V → ℕ) (v : V) (m : ℕ) (p : V → ℕ)
    (hp : valid G m (reduce G b v) p) : valid G (m + 1) b (addOne v p) := by
  refine ⟨?_, (covers_addOne_iff G b v p).mpr hp.2⟩
  rw [sum_addOne]
  simp only [Finset.mem_univ, if_true]
  have hsize := hp.1
  omega

theorem valid_eraseOne (b : V → ℕ) (v : V) (m : ℕ) (p : V → ℕ)
    (hp : valid G (m + 1) b p) (hv : 0 < p v) : valid G m (reduce G b v) (eraseOne v p) := by
  have heq := add_erase v p hv
  refine ⟨?_, (covers_addOne_iff G b v (eraseOne v p)).mp (by rw [heq]; exact hp.2)⟩
  have hs : (∑ u, eraseOne v p u) + 1 = ∑ u, p u := by
    have h := sum_addOne (Finset.univ : Finset V) v (eraseOne v p)
    rw [heq] at h
    simpa only [Finset.mem_univ, if_true] using h.symm
  have h := hp.1
  omega

noncomputable def search (t : ℝ) (c : V → ℝ) : ℕ → (V → ℕ) → Finset (V → ℕ)
  | 0, b => terminal G b 0 c
  | m + 1, b =>
    if 2 * (t + 1) * (m + 1 : ℕ) ≤ ((active b).card : ℝ) then
      (LocalSearchBounds.heavy G (active b) (m + 1)).biUnion (fun v =>
        (search t c m (reduce G b v)).image (addOne v))
    else terminal G b (m + 1) c

theorem search_sound (t : ℝ) (c : V → ℝ) (m : ℕ) (b : V → ℕ) {p : V → ℕ}
    (hp : p ∈ search G t c m b) : valid G m b p := by
  induction m generalizing b p with
  | zero => exact terminal_sound G b 0 c hp
  | succ m ih =>
    simp only [search] at hp
    split_ifs at hp with hlarge
    · obtain ⟨v, _, himg⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp himg
      exact valid_addOne G b v m p' (ih (reduce G b v) hp')
    · exact terminal_sound G b (m + 1) c hp

/-- Exactness: every bounded completion is matched by a returned completion
of no greater cost. This proof follows the actual recursive search. -/
theorem search_complete (t : ℝ) (ht : 1 ≤ t) (c : V → ℝ) (m : ℕ) (b : V → ℕ)
    (p : V → ℕ) (hp : valid G m b p) :
    ∃ p' ∈ search G t c m b, integerCost c p' ≤ integerCost c p := by
  induction m generalizing b p with
  | zero => exact terminal_complete G b 0 c p hp
  | succ m ih =>
    by_cases hlarge : 2 * (t + 1) * (m + 1 : ℕ) ≤ ((active b).card : ℝ)
    · have hA : (active b).Nonempty := by
        apply Finset.card_pos.mp
        have hpos : (0 : ℝ) < (active b).card := by
          have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
          nlinarith
        exact_mod_cast hpos
      have hcov : ∀ r ∈ active b, 1 ≤ ∑ v ∈ closed G r, p v := by
        intro r hr
        have hb := (Finset.mem_filter.mp hr).2
        have hc := hp.2 r
        omega
      obtain ⟨v, hv, hvp⟩ := LocalSearchBounds.completion_hits_heavy G (active b) hA
        (m + 1) (by omega) p hp.1 hcov
      have hvalid := valid_eraseOne G b v m p hp hvp
      obtain ⟨p', hp', hcost⟩ := ih (reduce G b v) (eraseOne v p) hvalid
      refine ⟨addOne v p', ?_, ?_⟩
      · rw [search, if_pos hlarge]
        exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨p', hp', rfl⟩⟩
      · have heq := add_erase v p hvp
        rw [cost_addOne]
        have h := cost_addOne c v (eraseOne v p)
        rw [heq] at h
        linarith
    · simpa only [search, if_neg hlarge] using terminal_complete G b (m + 1) c p hp
end Paper.ExactSearch
