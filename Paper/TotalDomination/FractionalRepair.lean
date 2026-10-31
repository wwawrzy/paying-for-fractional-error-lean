import Paper.TotalDomination.FractionalSolver

/-! Repair a uniform open-neighborhood fractional cover at the exceptional
low-degree vertices using one real adjacent vertex per exception. -/
namespace Paper.TotalDomination.FractionalRepair
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def repairNeighbor (hfree : ∀ v, (G.neighborFinset v).Nonempty) (v : V) : V :=
  (hfree v).choose

theorem repair_adj (hfree : ∀ v, (G.neighborFinset v).Nonempty) (v : V) :
    G.Adj v (repairNeighbor G hfree v) := (G.mem_neighborFinset v _).mp (hfree v).choose_spec

noncomputable def repairs (hfree : ∀ v, (G.neighborFinset v).Nonempty) (B : Finset V) : Finset V :=
  B.image (repairNeighbor G hfree)

noncomputable def vector (hfree : ∀ v, (G.neighborFinset v).Nonempty) (B : Finset V) (d : ℝ) (v : V) : ℝ := by
  classical
  exact 1/d+if v ∈ repairs G hfree B then 1 else 0

theorem feasible (hfree : ∀ v, (G.neighborFinset v).Nonempty) (B : Finset V) (d : ℝ) (hd : 0 < d)
    (hdeg : ∀ v ∉ B, d ≤ G.degree v) :
    CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ (vector G hfree B d) := by
  classical
  have hnon : ∀ v, 0 ≤ vector G hfree B d v := by intro v;unfold vector;positivity
  refine ⟨hnon,?_⟩
  intro r _
  by_cases hr : r ∈ B
  · let u := repairNeighbor G hfree r
    have hu : u ∈ repairs G hfree B := Finset.mem_image.mpr ⟨r,hr,rfl⟩
    have hv : 1 ≤ vector G hfree B d u := by
      simp only [vector,if_pos hu]
      have hh : (0:ℝ) ≤ 1/d := by positivity
      linarith
    exact hv.trans (Finset.single_le_sum (fun v _ => hnon v)
      ((G.mem_neighborFinset r u).mpr (repair_adj G hfree r)))
  · calc
      (1:ℝ) = d*(1/d) := by field_simp
      _ ≤ (G.degree r:ℝ)*(1/d) := mul_le_mul_of_nonneg_right (hdeg r hr) (by positivity)
      _ = ∑ _v ∈ G.neighborFinset r, (1/d:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by unfold vector;split_ifs <;> linarith)

theorem mass_bound (hfree : ∀ v, (G.neighborFinset v).Nonempty) (B : Finset V) (d : ℝ) :
    (∑ v, vector G hfree B d v) ≤ (Fintype.card V:ℝ)/d+B.card := by
  classical
  have hc : ((repairs G hfree B).card:ℝ) ≤ B.card := by exact_mod_cast Finset.card_image_le
  have he : (∑ v, if v ∈ repairs G hfree B then (1:ℝ) else 0) =
      (repairs G hfree B).card := by simp
  unfold vector
  rw [Finset.sum_add_distrib,he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
  linarith

theorem number_bound (hfree : ∀ v, (G.neighborFinset v).Nonempty) (B : Finset V) (d : ℝ) (hd : 0 < d)
    (hdeg : ∀ v ∉ B, d ≤ G.degree v) :
    CoveringOptimum.number (fun r => G.neighborFinset r) Finset.univ (fun _ => (1:ℝ)) ≤
      (Fintype.card V:ℝ)/d+B.card := by
  have hn : CoveringOptimum.number (fun r => G.neighborFinset r) Finset.univ
      (fun _ => (1:ℝ)) ≤ ∑ v, vector G hfree B d v := by
    apply csInf_le
    · refine ⟨0,?_⟩
      rintro z ⟨y,hy,rfl⟩
      change 0 ≤ ∑ v, (1:ℝ)*y v
      exact Finset.sum_nonneg (fun v _ => mul_nonneg zero_le_one (hy.1 v))
    · refine ⟨vector G hfree B d,feasible G hfree B d hd hdeg,?_⟩
      simp only [CoveringOptimum.objective,one_mul]

  exact hn.trans (mass_bound G hfree B d)

end Paper.TotalDomination.FractionalRepair
#print axioms Paper.TotalDomination.FractionalRepair.number_bound
