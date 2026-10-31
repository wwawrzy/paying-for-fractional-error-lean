import Paper.TotalDomination.CostSaving

namespace Paper.TotalDomination.HighGirthSavingArithmetic
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (I : Input G)

theorem density_counts (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G a) (hcut : I.cutoff = 3) :
    0 ≤ surplus G I ∧
    ((high G I).card : ℝ) ≤ a*surplus G I/(3-2*a) ∧
    ((served G I).card : ℝ) ≤ (3-a)*surplus G I/(3-2*a) ∧
    excess G I 1 ≤ a*surplus G I/(3-2*a) := by
  have hd : 0 < 3-2*a := by linarith
  have hH : ((high G I).card : ℝ) ≤ excess G I 1 := by
    calc
      _ = ∑ _v ∈ high G I, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hh := (Finset.mem_filter.mp hv).2
        rw [hcut] at hh
        have hhR : (3:ℝ) ≤ hits G I v := by exact_mod_cast hh
        change 1 ≤ (hits G I v : ℝ)-2*1
        linarith
  have heq : excess G I 1 = excess G I a + (2*a-2)*(high G I).card := by
    simp only [excess,Finset.sum_sub_distrib,Finset.sum_const,Finset.sum_mul,
      nsmul_eq_mul,mul_one]
    ring
  have hE := excess_le G I a hden
  have h0 := surplus_nonneg G I a (by linarith) hden (by rw [hcut]; norm_num; linarith)
  have hHb : ((high G I).card : ℝ) ≤ a*surplus G I/(3-2*a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hb : (3-2*a)*(a*surplus G I/(3-2*a)) = a*surplus G I := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hHb (show 0 ≤ 2*a-2 by linarith)
  have hEb : excess G I 1 ≤ a*surplus G I/(3-2*a) := by
    nlinarith [heq]
  refine ⟨h0,hHb,?_,hEb⟩
  have hsj : ((served G I).card : ℝ) = (high G I).card+surplus G I := by
    unfold surplus; ring
  apply (le_div_iff₀ hd).mpr
  have hHmul := (le_div_iff₀ hd).mp hHb
  rw [hsj]
  nlinarith only [hHmul]

theorem beta_pos (a : ℝ) (hhi : a < 9/8) :
    0 < (9-8*a)/(3*(3-2*a)) := by
  apply div_pos <;> linarith

end Paper.TotalDomination.HighGirthSavingArithmetic
