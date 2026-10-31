import Paper.Certificates.Counting.FloatingStep

/-! Terminating weighted floating rounding with strict loss <a in every row.
The proof uses induction on the actual number of fractional coordinates. -/
namespace Paper.FloatingRound
attribute [local instance] Classical.propDecidable
open FloatingCore
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem small_row_loss (T : Finset I) (a : ℕ) (ha : 1 ≤ a) (y z : I → ℝ)
    (hsmall : (T ∩ floating y).card ≤ a) (hz : ∀ i, 0 ≤ z i)
    (hfixed : ∀ i ∉ floating y, z i = y i) :
    (∑ i ∈ T, y i) - (∑ i ∈ T, z i) < a := by
  classical
  have heq : (∑ i ∈ T ∩ floating y, (y i - z i)) = ∑ i ∈ T, (y i - z i) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hn
    have hiF : i ∉ floating y := fun hf => hn (Finset.mem_inter.mpr ⟨hi, hf⟩)
    rw [hfixed i hiF, sub_self]
  rw [← Finset.sum_sub_distrib, ← heq]
  by_cases hnon : (T ∩ floating y).Nonempty
  · have hlt : (∑ i ∈ T ∩ floating y, (y i - z i)) <
        ∑ _i ∈ T ∩ floating y, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hnon
      intro i hi
      have hy := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2.2
      linarith [hz i]
    have hcard : ((T ∩ floating y).card : ℝ) ≤ a := by exact_mod_cast hsmall
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
    exact hlt.trans_le hcard
  · have he : T ∩ floating y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    rw [he, Finset.sum_empty]
    exact_mod_cast (by omega : 0 < a)

/-- Integral coordinates remain fixed, cost does not increase, and each row
loses strictly less than a, even when equations cease to be active. -/
theorem round (N : J → Finset I) (a : ℕ) (ha : 1 ≤ a) (c y : I → ℝ)
    (hbox : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hcap : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ a) :
    ∃ z : I → ℝ, (∀ i, z i = 0 ∨ z i = 1) ∧
      (∀ i ∉ floating y, z i = y i) ∧
      (∑ i, c i * z i) ≤ (∑ i, c i * y i) ∧
      ∀ r, (∑ i ∈ N r, y i) - (∑ i ∈ N r, z i) < a := by
  classical
  suffices h : ∀ n (y : I → ℝ), (floating y).card = n →
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
      ∃ z : I → ℝ, (∀ i, z i = 0 ∨ z i = 1) ∧
        (∀ i ∉ floating y, z i = y i) ∧
        (∑ i, c i * z i) ≤ (∑ i, c i * y i) ∧
        ∀ r, (∑ i ∈ N r, y i) - (∑ i ∈ N r, z i) < a from
    h _ y rfl hbox
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hyn hy
    by_cases hnon : (floating y).Nonempty
    · obtain ⟨p, hpbox, hpfix, hprows, hpcost, hlt⟩ := FloatingStep.step N a y c hy hnon hcap
      obtain ⟨z, hzint, hzfix, hzcost, hzrows⟩ := ih (floating p).card
        (by omega) p rfl hpbox
      have hsub : floating p ⊆ floating y := by
        intro i hi
        by_contra hn
        have hh := (Finset.mem_filter.mp hi).2
        have he := hpfix i hn
        rw [he] at hh
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
      have hfix : ∀ i ∉ floating y, z i = y i := by
        intro i hi
        have hn : i ∉ floating p := fun hp => hi (hsub hp)
        exact (hzfix i hn).trans (hpfix i hi)
      refine ⟨z, hzint, hfix, hzcost.trans hpcost, ?_⟩
      intro r
      by_cases hr : r ∈ active N a (floating y)
      · rw [← hprows r hr]
        exact hzrows r
      · have hsmall : (N r ∩ floating y).card ≤ a := by
          have hn : ¬ a < (N r ∩ floating y).card := by
            intro h
            exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          omega
        apply small_row_loss (N r) a ha y z hsmall _ hfix
        intro i
        rcases hzint i with hi | hi <;> rw [hi] <;> norm_num
    · have hint : ∀ i, y i = 0 ∨ y i = 1 := by
        intro i
        by_cases hz : y i = 0
        · exact Or.inl hz
        · right
          have hy0 : 0 < y i := lt_of_le_of_ne (hy i).1 (Ne.symm hz)
          have hn : ¬ y i < 1 := by
            intro h
            exact hnon ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0, h⟩⟩
          linarith [(hy i).2]
      refine ⟨y, hint, fun _ _ => rfl, le_rfl, ?_⟩
      intro r
      rw [sub_self]
      exact_mod_cast (by omega : 0 < a)
end Paper.FloatingRound
