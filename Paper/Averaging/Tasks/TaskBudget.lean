import Paper.Averaging.Tasks.TaskOptimum
import Paper.Preliminaries.OptimumComparison

/-! Selecting the actual task owners is a feasible physical task vector
of cost at most B0 times the number of owners in the part. -/
namespace Paper.TaskBudget
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem centers_subset (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q)) :
    PhysicalTasks.centers D Q I ⊆ PhysicalTasks.vertices G D R L Q I := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  exact PhysicalTasks.root_mem G D R L Q I i hi

set_option maxHeartbeats 1000000 in
theorem owner_vector (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    (c : V → ℝ) (B₀ : ℝ) (hcost : ∀ v, c v ≤ B₀) :
    let H := PhysicalTasks.vertices G D R L Q I
    let T := InducedSubsets.lift H (OwnerTasks.demands G D R L Q I B)
    ∃ x : ↥(H : Set V) → ℝ, PartialOptimum.Feasible (G.induce (H : Set V)) T x ∧
      PartialOptimum.objective (fun v => c v.val) x ≤ B₀ * I.card := by
  classical
  dsimp only
  let H := PhysicalTasks.vertices G D R L Q I
  let C := PhysicalTasks.centers D Q I
  let T := InducedSubsets.lift H (OwnerTasks.demands G D R L Q I B)
  let x := InducedCover.mask H C (fun _ => (1 : ℝ))
  have hCH : C ⊆ H := centers_subset G D R L Q I
  have hx : ∀ v, 0 ≤ x v := by
    intro v
    dsimp only [x, InducedCover.mask]
    split_ifs <;> norm_num
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · intro r hr
    have hrT : r.val ∈ OwnerTasks.demands G D R L Q I B := Finset.mem_subtype.mp hr
    obtain ⟨d, hdC, hrd⟩ := Finset.mem_biUnion.mp (PhysicalTasks.owner_cover G D R L Q I B hrT)
    let u : ↥(H : Set V) := ⟨d, hCH hdC⟩
    have hdu : d ∈ closed G r.val := (closed_symm G r.val d).mp hrd
    have hu : u ∈ closed (G.induce (H : Set V)) r :=
      (mem_closed (G.induce (H : Set V)) u r).mpr
        (((mem_closed G d r.val).mp hdu).elim (fun he => Or.inl (Subtype.ext he)) Or.inr)
    have hs := Finset.single_le_sum (fun v (_ : v ∈ closed (G.induce (H : Set V)) r) => hx v) hu
    have hxu : x u = 1 := by
      change (if d ∈ C then (1 : ℝ) else 0) = 1
      exact if_pos hdC
    rw [hxu] at hs
    exact hs
  · have hc : PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) x = ∑ d ∈ C, c d := by
      simpa only [x, mul_one] using InducedCover.mask_cost H C hCH c (fun _ => (1 : ℝ))
    rw [hc]
    calc
      _ ≤ ∑ _d ∈ C, B₀ := Finset.sum_le_sum (fun d _ => hcost d)
      _ = B₀ * I.card := by simp only [Finset.sum_const, nsmul_eq_mul, C, PhysicalTasks.centers_card]; ring

theorem optimum_bound (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) (B₀ : ℝ) (hcost : ∀ v, c v ≤ B₀) :
    TaskOptimum.number G D R L Q I B c ≤ B₀ * I.card := by
  obtain ⟨x, hx, hxcost⟩ := owner_vector G D R L Q I B c B₀ hcost
  exact (OptimumComparison.le_feasible _ _ _ x (fun v => hc v.val) hx).trans hxcost
end Paper.TaskBudget
