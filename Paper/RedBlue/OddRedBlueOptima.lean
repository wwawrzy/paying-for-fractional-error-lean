import Paper.RedBlue.OddRedBlueCode
namespace Paper.OddRedBlue
open scoped BigOperators
open SevenFoundation OddPathPower

theorem fractional_lower (m : ℕ) (p : Fin 2) (x : Fin (8*m) → ℝ)
    (hx : CoveringOptimum.Feasible (RedBlue.rows (graph (8*m) 3) (red m p) (blue m p)) (red m p) x) :
    (m:ℝ) ≤ ∑ v, x v := by
  have hrow : ∀ r ∈ packing m p, (1:ℝ) ≤ ∑ v ∈ (graph (8*m) 3).neighborFinset r, x v := by
    intro r hr
    have hred := packing_red m p hr
    have h := hx.2 r hred
    rw [RedBlue.rows,if_pos hred] at h
    exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun v _ _ => hx.1 v))
  have hs : (m:ℝ) ≤ ∑ r ∈ packing m p, ∑ v ∈ (graph (8*m) 3).neighborFinset r, x v := by
    calc
      _ = ∑ _r ∈ packing m p, (1:ℝ) := by simp [packing_card]
      _ ≤ _ := Finset.sum_le_sum hrow
  rw [TotalDomination.HighGirthSelection.open_incidence_sum] at hs
  refine hs.trans ?_
  apply Finset.sum_le_sum
  intro v hv
  have hc : ((((graph (8*m) 3).neighborFinset v ∩ packing m p).card):ℝ) ≤ 1 := by
    exact_mod_cast packing_neighbor_count m p v
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (hx.1 v)

theorem indicator_feasible (m : ℕ) (p : Fin 2) (S : Finset (Fin (8*m)))
    (hS : S ⊆ blue m p) (hcov : ∀ r ∈ red m p, ∃ v ∈ S, (graph (8*m) 3).Adj r v) :
    CoveringOptimum.Feasible (RedBlue.rows (graph (8*m) 3) (red m p) (blue m p)) (red m p) (indicator S) := by
  classical
  have hnon : ∀ v, (0:ℝ) ≤ indicator S v := by intro v;unfold indicator;split_ifs <;> norm_num
  refine ⟨hnon,?_⟩
  intro r hr
  obtain ⟨v,hv,ha⟩ := hcov r hr
  have hm := Finset.single_le_sum (fun u _ => hnon u)
    ((RedBlue.mem_rows _ _ _ _ _).mpr ⟨hr,ha,hS hv⟩)
  simpa only [indicator,if_pos hv] using hm

theorem integral_lower (m : ℕ) (p : Fin 2) (S : Finset (Fin (8*m)))
    (hS : S ⊆ blue m p) (hcov : ∀ r ∈ red m p, ∃ v ∈ S, (graph (8*m) 3).Adj r v) : m ≤ S.card := by
  have h := fractional_lower m p (indicator S) (indicator_feasible m p S hS hcov)
  have hR : (m:ℝ) ≤ S.card := by
    simpa only [indicator,Finset.sum_ite_mem,Finset.sum_const,Finset.inter_univ,Finset.univ_inter,Finset.card_univ,nsmul_eq_mul,mul_one] using h
  exact_mod_cast hR

theorem fractional_number (m : ℕ) (p : Fin 2) :
    CoveringOptimum.number (RedBlue.rows (graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ)) = m := by
  classical
  let C := RedBlue.rows (graph (8*m) 3) (red m p) (blue m p)
  have hrows : ∀ r ∈ red m p, (C r).Nonempty := by
    intro r hr
    obtain ⟨v,hv,ha⟩ := covers m p r hr
    exact ⟨v,(RedBlue.mem_rows _ _ _ _ _).mpr ⟨hr,ha,code_blue m p hv⟩⟩
  obtain ⟨x,hx,he⟩ := CoveringOptimum.exists_optimum_eq_number C (red m p) (fun _ => (1:ℝ)) hrows (fun _ => zero_le_one)
  have hlo := fractional_lower m p x hx
  have hhigh : CoveringOptimum.number C (red m p) (fun _ => (1:ℝ)) ≤ m := by
    apply csInf_le
    · refine ⟨0,?_⟩
      rintro z ⟨y,hy,rfl⟩
      exact Finset.sum_nonneg fun v _ => mul_nonneg zero_le_one (hy.1 v)
    · refine ⟨indicator (code m p),indicator_feasible m p _ (code_blue m p) (covers m p),?_⟩
      simp [CoveringOptimum.objective,indicator,code_card]
  simp only [CoveringOptimum.objective,one_mul] at he
  exact le_antisymm hhigh (by linarith)

/-- The fractional and integral red-blue optima both equal m, for either
choice of the two sides as demands. -/
theorem exact_optima (m : ℕ) (p : Fin 2) :
    CoveringOptimum.number (RedBlue.rows (graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ)) = m ∧
    (code m p).card=m ∧ code m p ⊆ blue m p ∧
    (∀ r ∈ red m p, ∃ v ∈ code m p, (graph (8*m) 3).Adj r v) ∧
    (∀ S : Finset (Fin (8*m)), S ⊆ blue m p →
      (∀ r ∈ red m p, ∃ v ∈ S, (graph (8*m) 3).Adj r v) → m ≤ S.card) := by
  exact ⟨fractional_number m p,code_card m p,code_blue m p,covers m p,integral_lower m p⟩
end Paper.OddRedBlue
#print axioms Paper.OddRedBlue.exact_optima
