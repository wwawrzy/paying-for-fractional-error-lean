import Paper.Averaging.Tasks.TaskCostSum

/-! Integral task optima for arbitrary covering sets. The restriction argument
uses disjoint useful candidate sets, not disjoint communication regions.
These are optimization statements; they do not assert a distributed runtime. -/
namespace Paper.GeneralIntegralTasks

open scoped BigOperators
variable {V I : Type*} [DecidableEq V]

def Covers (C : V → Finset V) (R Z : Finset V) : Prop :=
  ∀ r ∈ R, ∃ v ∈ Z, v ∈ C r

def useful (C : V → Finset V) (R : Finset V) : Finset V :=
  R.biUnion C

def cost (c : V → ℝ) (Z : Finset V) : ℝ := ∑ v ∈ Z, c v

/-- Restricting a cover to the candidates used by a task preserves coverage. -/
theorem restrict_covers (C : V → Finset V) (R T O : Finset V)
    (hT : T ⊆ R) (hO : Covers C R O) :
    Covers C T (O ∩ useful C T) := by
  intro r hr
  obtain ⟨v, hvO, hvC⟩ := hO r (hT hr)
  exact ⟨v, Finset.mem_inter.mpr ⟨hvO, Finset.mem_biUnion.mpr ⟨r, hr, hvC⟩⟩, hvC⟩

/-- A finite admissible region with a feasible witness has an attained optimum. -/
theorem exists_optimum (C : V → Finset V) (T H : Finset V) (c : V → ℝ)
    (W : Finset V) (hWH : W ⊆ H) (hW : Covers C T W) :
    ∃ Z : Finset V, Z ⊆ H ∧ Covers C T Z ∧
      ∀ O : Finset V, O ⊆ H → Covers C T O → cost c Z ≤ cost c O := by
  classical
  let F := H.powerset.filter (Covers C T)
  have hWF : W ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hWH, hW⟩
  obtain ⟨Z, hZF, hmin⟩ := Finset.exists_min_image F (cost c) ⟨W, hWF⟩
  obtain ⟨hZH, hZ⟩ := Finset.mem_filter.mp hZF
  exact ⟨Z, Finset.mem_powerset.mp hZH, hZ,
    fun O hOH hO => hmin O (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hOH, hO⟩)⟩

/-- The public copy budget bounds an optimal integral cover when costs are
at least one and a feasible witness has cost within that budget. -/
theorem exists_bounded_optimum (C : V → Finset V) (T H : Finset V) (c : V → ℝ)
    (hc : ∀ v ∈ H, 1 ≤ c v) (M : ℕ)
    (W : Finset V) (hWH : W ⊆ H) (hW : Covers C T W) (hcost : cost c W ≤ M) :
    ∃ Z : Finset V, Z ⊆ H ∧ Covers C T Z ∧ Z.card ≤ M ∧
      ∀ O : Finset V, O ⊆ H → Covers C T O → cost c Z ≤ cost c O := by
  obtain ⟨Z, hZH, hZ, hmin⟩ := exists_optimum C T H c W hWH hW
  have hcard : (Z.card : ℝ) ≤ cost c Z := by
    calc
      _ = ∑ _v ∈ Z, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hc v (hZH hv))
  have hb : (Z.card : ℝ) ≤ (M : ℝ) := hcard.trans ((hmin W hWH hW).trans hcost)
  exact ⟨Z, hZH, hZ, by exact_mod_cast hb, hmin⟩

/-- Simultaneously choose exact task optima. Their total cost is bounded by
every global cover, even if the physical task regions overlap. -/
theorem exists_optimal_tasks [Fintype V] [DecidableEq I]
    (C : V → Finset V) (R : Finset V) (P : Finset I)
    (T H : I → Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hTR : ∀ i ∈ P, T i ⊆ R)
    (hH : ∀ i ∈ P, useful C (T i) ⊆ H i)
    (hd : (P : Set I).PairwiseDisjoint (fun i => useful C (T i)))
    (W : Finset V) (hW : Covers C R W) :
    ∃ Z : I → Finset V,
      (∀ i ∈ P, Z i ⊆ H i ∧ Covers C (T i) (Z i) ∧
        ∀ O : Finset V, O ⊆ H i → Covers C (T i) O → cost c (Z i) ≤ cost c O) ∧
      ∀ O : Finset V, Covers C R O → (∑ i ∈ P, cost c (Z i)) ≤ cost c O := by
  classical
  have hex (i : I) (hi : i ∈ P) := exists_optimum C (T i) (H i) c
    (W ∩ useful C (T i))
    (fun _ hv => hH i hi (Finset.mem_inter.mp hv).2)
    (restrict_covers C R (T i) W (hTR i hi) hW)
  choose Z hZ using hex
  let result : I → Finset V := fun i => if hi : i ∈ P then Z i hi else ∅
  have hs (i : I) (hi : i ∈ P) :
      result i ⊆ H i ∧ Covers C (T i) (result i) ∧
        ∀ O : Finset V, O ⊆ H i → Covers C (T i) O → cost c (result i) ≤ cost c O := by
    simpa only [result, dif_pos hi] using hZ i hi
  refine ⟨result, hs, ?_⟩
  intro O hO
  let S : I → Finset V := fun i => O ∩ useful C (T i)
  have hdisj : (P : Set I).PairwiseDisjoint S := by
    intro i hi j hj hne
    exact (hd hi hj hne).mono Finset.inter_subset_right Finset.inter_subset_right
  calc
    _ ≤ ∑ i ∈ P, cost c (S i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hs i hi).2.2 (S i)
        (fun _ hv => hH i hi (Finset.mem_inter.mp hv).2)
        (restrict_covers C R (T i) O (hTR i hi) hO)
    _ = ∑ v ∈ P.biUnion S, c v := (Finset.sum_biUnion hdisj).symm
    _ ≤ cost c O := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
        exact (Finset.mem_inter.mp hi).1
      · intro v _ _
        exact hc v

end Paper.GeneralIntegralTasks

#print axioms Paper.GeneralIntegralTasks.exists_bounded_optimum
#print axioms Paper.GeneralIntegralTasks.exists_optimal_tasks
