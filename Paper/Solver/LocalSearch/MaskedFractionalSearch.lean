import Paper.Solver.LocalSearch.FractionalSearch
import Paper.Solver.LocalSearch.ActiveRecursiveSearch
import Paper.Averaging.Tasks.MaskedTaskCover
import Paper.Solver.LocalSearch.WordFractional

/-! The actual broadcast solver attains the task fractional approximation
with fixed common denominator and no global solution/cost oracle. -/
namespace Paper.MaskedFractionalSearch
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (L : ℕ) (Q : Finset D) (I J : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (a : ℕ) (ha' : 1 ≤ a)
    (hden : MinorDensity.Bound G (a : ℝ)) (B : ℕ) (c : V → Fin (B + 1))
    (hc' : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    {bits : ℕ} (C : BitCode V bits) (s : V → FractionalSearch.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ OwnerTasks.demands G D R L Q I J)) :
    let H := PhysicalTasks.vertices G D R L Q I
    let T := OwnerTasks.demands G D R L Q I J
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    let p := fun v => ((FractionalSearch.program C (4 * k) a B q M).run (MaskedTaskGraph.graph G (PhysicalTasks.vertices G D R L Q I)) s v).val
    let z := fun v : ↥(H : Set V) => (p v.val : ℝ) / q
    PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H T) z ∧
      PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) z ≤
        (1 + ξ) * TaskOptimum.number G D R L Q I J (fun v => ((c v).val : ℝ)) ∧
      (∀ v, (q : ℝ) * z v = p v.val) ∧ (∀ v, v ∉ H → p v = 0) := by
  dsimp only
  let H := PhysicalTasks.vertices G D R L Q I
  let T := OwnerTasks.demands G D R L Q I J
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  let b := TaskBenchmark.demand (q := q) T
  let input := fun v => FractionalSearch.searchInput q (s v)
  let solver := RecursiveSearch.program C (4 * k) a B q M
  have hai : ∀ v, (input v).active = decide (v ∈ H) := ha
  have hci : ∀ v, (input v).cost = c v := hc
  have hbi : ∀ v, (input v).value = b v := by
    intro v
    apply Fin.ext
    change (if (s v).demand then q else 0) = if v ∈ T then q else 0
    rw [hd v]
    change (if decide (v ∈ T) then q else 0) = if v ∈ T then q else 0
    by_cases hv : v ∈ T <;> simp [hv]
  have hz : ∀ v, v ∉ H → (b v).val = 0 :=
    TaskBenchmark.demand_outside H T (PhysicalTasks.demands_subset G D R L Q I J)
  have hspec := ActiveRecursiveSearch.correct
    (MaskedTaskGraph.graph G H) (ActiveTask.physicalMasked G D R L Q I hI k hsize) a ha'
    (MinorDensity.induced_bound (MaskedTaskGraph.graph G H) (MaskedTaskGraph.density G H hden))
    B q c C M b input hai hci hbi hz
  obtain ⟨benchmark, hbenchsize, hbenchsupport, hbenchcover, hbenchcost⟩ :=
    TaskBenchmark.exists_benchmark G D R L Q I J k hsize a ha' hden B c hc' ξ hξ
  have hbenchcoverMask := MaskedTaskCover.cover G H (fun r => (b r).val) benchmark
    hz hbenchsupport hbenchcover
  obtain ⟨i⟩ := hI.nonempty
  let v0 := i.val.val.val
  have hv0 : v0 ∈ H := PhysicalTasks.root_mem G D R L Q I i.val i.property
  obtain ⟨w, hw, hcostw⟩ := hspec.complete benchmark hbenchsize hbenchsupport hbenchcoverMask v0 hv0
  have hvalid := MaskedTaskCover.valid_original G H c b w (hspec.sound v0 hv0 w hw)
  have hrun : ∀ v ∈ H, solver.run (MaskedTaskGraph.graph G (PhysicalTasks.vertices G D R L Q I)) input v = some w :=
    fun v hv => (hspec.uniform v v0 hv hv0).trans hw
  have hcopies : ∀ v, ((FractionalSearch.program C (4 * k) a B q M).run (MaskedTaskGraph.graph G (PhysicalTasks.vertices G D R L Q I)) s v).val = SolutionWord.copies w v := by
    intro v
    rw [FractionalSearch.run_program, ha v]
    by_cases hv : v ∈ H
    · simp only [show decide (v ∈ PhysicalTasks.vertices G D R L Q I) = true from decide_eq_true hv,
        ↓reduceIte]
      rw [hrun v hv]
      exact FractionalSearch.count_some w hvalid.1 v
    · have hzero := SearchSpec.copies_support G H c b M w hvalid v hv
      simp only [show decide (v ∈ PhysicalTasks.vertices G D R L Q I) = false from decide_eq_false hv,
        Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
      exact hzero.symm
  have hwf := WordFractional.spec G H T (LocalSolverMath.denominator_pos a ξ) c w hvalid
  have hzvec : (fun v : ↥(H : Set V) =>
      (((FractionalSearch.program C (4 * k) a B q M).run (MaskedTaskGraph.graph G (PhysicalTasks.vertices G D R L Q I)) s v.val).val : ℝ) / q) = WordFractional.vector H q w := by
    funext v
    rw [hcopies v.val]
    rfl
  rw [hzvec]
  refine ⟨hwf.1, ?_, ?_, ?_⟩
  · rw [hwf.2.1]
    exact (div_le_div_of_nonneg_right (show (SolutionWord.cost w : ℝ) ≤
      IntegralTable.cost (fun v => (c v).val) benchmark by exact_mod_cast hcostw) (Nat.cast_nonneg q)).trans hbenchcost
  · intro v
    rw [hcopies v.val]
    exact hwf.2.2 v
  · intro v hv
    rw [hcopies v]
    exact SearchSpec.copies_support G H c b M w hvalid v hv
end Paper.MaskedFractionalSearch
