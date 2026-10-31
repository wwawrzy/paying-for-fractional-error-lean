import Paper.Certificates.Counting.FloatingCore

/-! Extend the finite kernel direction by zero and perform one genuine
cost-nonincreasing floating-variable step. -/
namespace Paper.FloatingStep
attribute [local instance] Classical.propDecidable
open FloatingCore
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def extend (F : Finset I) (z : F → ℝ) (i : I) : ℝ :=
  if h : i ∈ F then z ⟨i, h⟩ else 0

theorem sum_extend (F : Finset I) (z : F → ℝ) (c : I → ℝ) :
    (∑ i, c i * extend F z i) = ∑ i : F, c i.val * z i := by
  classical
  calc
    _ = ∑ i ∈ F, c i * extend F z i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [extend, dif_neg hi, mul_zero]
    _ = ∑ i : F, c i.val * extend F z i.val :=
      Finset.sum_subtype F (fun i => by rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [extend, dif_pos i.property]

theorem row_sum (N : Finset I) (w : I → ℝ) :
    (∑ i ∈ N, w i) = ∑ i, (if i ∈ N then (1 : ℝ) else 0) * w i := by
  classical
  have heq : (Finset.univ : Finset I).filter (fun i => i ∈ N) = N := by ext i; simp
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter, heq]

/-- A direction preserves every currently large row and does not increase cost. -/
theorem exists_direction (N : J → Finset I) (a : ℕ) (y c : I → ℝ)
    (hF : (floating y).Nonempty)
    (hcap : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ a) :
    ∃ w : I → ℝ, w ≠ 0 ∧ (∀ i ∉ floating y, w i = 0) ∧
      (∀ r ∈ active N a (floating y), ∑ i ∈ N r, w i = 0) ∧
      ∑ i, c i * w i ≤ 0 := by
  classical
  let F := floating y
  let A := active N a F
  let M : Matrix A F ℝ := fun r i => if i.val ∈ N r.val then 1 else 0
  let L := Matrix.mulVecLin M
  have hcard : Fintype.card A < Fintype.card F := by
    simpa only [Fintype.card_coe] using active_card_lt N a F hF hcap
  obtain ⟨z, hz, hzero, hcost⟩ := descent_kernel L (fun i => c i.val) hcard
  refine ⟨extend F z, ?_, ?_, ?_, ?_⟩
  · intro heq
    apply hz
    funext i
    have h := congrFun heq i.val
    simpa only [extend, dif_pos i.property, Pi.zero_apply] using h
  · intro i hi
    exact dif_neg hi
  · intro r hr
    rw [row_sum, sum_extend]
    have h := congrFun hzero (⟨r, hr⟩ : A)
    simpa only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Pi.zero_apply] using h
  · rw [sum_extend]
    exact hcost

/-- One step reduces the floating support, fixes all integral coordinates,
preserves active rows, and weakly decreases the weighted objective. -/
theorem step (N : J → Finset I) (a : ℕ) (y c : I → ℝ)
    (hbox : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hF : (floating y).Nonempty)
    (hcap : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ a) :
    ∃ z : I → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ i ∉ floating y, z i = y i) ∧
      (∀ r ∈ active N a (floating y), ∑ i ∈ N r, z i = ∑ i ∈ N r, y i) ∧
      (∑ i, c i * z i) ≤ (∑ i, c i * y i) ∧
      (floating z).card < (floating y).card := by
  obtain ⟨w, hw, hsupport, hrow, hcost⟩ := exists_direction N a y c hF hcap
  have hs : ∀ i, w i ≠ 0 → 0 < y i ∧ y i < 1 := by
    intro i hi
    have hf : i ∈ floating y := by
      by_contra hn
      exact hi (hsupport i hn)
    exact (Finset.mem_filter.mp hf).2
  obtain ⟨t, ht, hbounds, _, hlt⟩ := box_step y w hbox hw hs
  refine ⟨fun i => y i + t * w i, hbounds, ?_, ?_, ?_, hlt⟩
  · intro i hi
    simp only [hsupport i hi, mul_zero, add_zero]
  · intro r hr
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hrow r hr, mul_zero, add_zero]
  · have heq : (∑ i, c i * (y i + t * w i)) =
        (∑ i, c i * y i) + t * ∑ i, c i * w i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    have h := mul_nonpos_of_nonneg_of_nonpos ht.le hcost
    linarith
end Paper.FloatingStep
