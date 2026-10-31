import Mathlib

/-! Finite linear-algebra core for weighted floating-variable rounding.
No graph APIs or unproved rounding hypotheses are used. -/
namespace Paper.FloatingCore
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def floating (y : I → ℝ) : Finset I :=
  Finset.univ.filter (fun v => 0 < y v ∧ y v < 1)

noncomputable def active (N : J → Finset I) (a : ℕ) (F : Finset I) : Finset J :=
  Finset.univ.filter (fun r => a < (N r ∩ F).card)

theorem incidence_sum (N : J → Finset I) (A : Finset J) (F : Finset I) :
    (∑ r ∈ A, (N r ∩ F).card) = ∑ v ∈ F, (A.filter (fun r => v ∈ N r)).card := by
  classical
  have heq : ∀ r, N r ∩ F = F.filter (fun v => v ∈ N r) := by
    intro r
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact and_comm
  simp_rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem active_card_lt (N : J → Finset I) (a : ℕ) (F : Finset I) (hF : F.Nonempty)
    (hcap : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ a) :
    (active N a F).card < F.card := by
  classical
  have hlow : (a + 1) * (active N a F).card ≤ ∑ r ∈ active N a F, (N r ∩ F).card := by
    calc
      _ = ∑ _r ∈ active N a F, (a + 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun r hr => by
        have h := (Finset.mem_filter.mp hr).2
        omega)
  have hhigh : (∑ r ∈ active N a F, (N r ∩ F).card) ≤ a * F.card := by
    rw [incidence_sum]
    calc
      _ ≤ ∑ _v ∈ F, a := Finset.sum_le_sum (fun v _ =>
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hcap v))
      _ = _ := by simp [mul_comm]
  have hpos := Finset.card_pos.mpr hF
  nlinarith

/-- Fewer equations than variables give a nonzero direction of nonincreasing
weighted cost. Negating a kernel vector handles the sign of the objective. -/
theorem descent_kernel (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (c : I → ℝ)
    (hcard : Fintype.card J < Fintype.card I) :
    ∃ w : I → ℝ, w ≠ 0 ∧ L w = 0 ∧ ∑ i, c i * w i ≤ 0 := by
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_pi] using hcard)
  obtain ⟨w, hwk, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hzero : L w = 0 := hwk
  by_cases hc : (∑ i, c i * w i) ≤ 0
  · exact ⟨w, hw, hzero, hc⟩
  · refine ⟨-w, neg_ne_zero.mpr hw, ?_, ?_⟩
    · simp only [map_neg, hzero, neg_zero]
    · simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith

/-- Move a nonzero direction supported on fractional coordinates until a first
coordinate hits the boundary of the unit cube. -/
theorem box_step (y w : I → ℝ) (hbox : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hw : w ≠ 0) (hsupport : ∀ i, w i ≠ 0 → 0 < y i ∧ y i < 1) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ y i + t * w i ∧ y i + t * w i ≤ 1) ∧
      floating (fun i => y i + t * w i) ⊆ floating y ∧
      (floating (fun i => y i + t * w i)).card < (floating y).card := by
  classical
  let S := Finset.univ.filter (fun i => w i ≠ 0)
  have hS : S.Nonempty := by
    by_contra hn
    apply hw
    funext i
    by_contra hi
    exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let limit := fun i => if 0 < w i then (1 - y i) / w i else y i / (-w i)
  have hlim : ∀ i ∈ S, 0 < limit i := by
    intro i hi
    have hne : w i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hy := hsupport i hne
    dsimp [limit]
    split_ifs with hp
    · exact div_pos (by linarith) hp
    · exact div_pos hy.1 (by have := lt_of_le_of_ne (le_of_not_gt hp) hne; linarith)
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image S limit hS
  let t := limit i0
  have ht : 0 < t := hlim i0 hi0
  have hbounds : ∀ i, 0 ≤ y i + t * w i ∧ y i + t * w i ≤ 1 := by
    intro i
    by_cases hz : w i = 0
    · simpa only [hz, mul_zero, add_zero] using hbox i
    have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hle : t ≤ limit i := hmin i hi
    by_cases hp : 0 < w i
    · have hle' : t * w i ≤ 1 - y i := (le_div_iff₀ hp).mp (by
        simpa only [limit, if_pos hp] using hle)
      have hprod : 0 ≤ t * w i := mul_nonneg ht.le hp.le
      constructor <;> linarith [(hbox i).1]
    · have hn : 0 < -w i := by
        have := lt_of_le_of_ne (le_of_not_gt hp) hz
        linarith
      have hle' : t * (-w i) ≤ y i := (le_div_iff₀ hn).mp (by
        simpa only [limit, if_neg hp] using hle)
      have hprod : t * w i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hp)
      constructor <;> nlinarith [(hbox i).2]
  have hi0ne : w i0 ≠ 0 := (Finset.mem_filter.mp hi0).2
  have hit : y i0 + t * w i0 = 0 ∨ y i0 + t * w i0 = 1 := by
    by_cases hp : 0 < w i0
    · right
      have hmul : t * w i0 = 1 - y i0 := by
        dsimp [t, limit]
        rw [if_pos hp, div_mul_cancel₀ _ (ne_of_gt hp)]
      linarith
    · left
      have hn : 0 < -w i0 := by
        have := lt_of_le_of_ne (le_of_not_gt hp) hi0ne
        linarith
      have hmul : t * (-w i0) = y i0 := by
        dsimp [t, limit]
        rw [if_neg hp, div_mul_cancel₀ _ (ne_of_gt hn)]
      nlinarith
  have hsub : floating (fun i => y i + t * w i) ⊆ floating y := by
    intro i hi
    by_cases hz : w i = 0
    · have hh := (Finset.mem_filter.mp hi).2
      change 0 < y i + t * w i ∧ y i + t * w i < 1 at hh
      rw [hz, mul_zero, add_zero] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport i hz⟩
  have hi0F : i0 ∈ floating y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport i0 hi0ne⟩
  have hi0not : i0 ∉ floating (fun i => y i + t * w i) := by
    intro hi
    have hh := (Finset.mem_filter.mp hi).2
    change 0 < y i0 + t * w i0 ∧ y i0 + t * w i0 < 1 at hh
    rcases hit with hzero | hone
    · rw [hzero] at hh
      linarith
    · rw [hone] at hh
      linarith
  refine ⟨t, ht, hbounds, hsub, Finset.card_lt_card ?_⟩
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  exact hi0not (heq.symm ▸ hi0F)

end Paper.FloatingCore
