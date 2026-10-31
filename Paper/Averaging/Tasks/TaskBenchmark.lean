import Paper.Averaging.Tasks.TaskSolverMath
import Paper.Preliminaries.NatExtension

/-! A supported finite-budget integer benchmark for the actual broadcast
search, extracted from the already proved weighted fractional certificate.
Only this proof witness uses global induced-task mathematics. -/
namespace Paper.TaskBenchmark
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]

theorem best_sound (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (c : V → ℝ)
    (M : ℕ) (b : V → ℕ) (p : V → ℕ) (hp : LocalFractional.best G t c M b = some p) :
    FiniteSearch.valid G M b p := by
  classical
  unfold LocalFractional.best at hp
  split_ifs at hp with hn
  have hh := (Finset.exists_min_image (ExactSearch.search G t c M b) (FiniteSearch.integerCost c) hn).choose_spec
  have he := Option.some.inj hp
  subst p
  exact ExactSearch.search_sound G t c M b hh.1

def demand {q : ℕ} (T : Finset V) (r : V) : Fin (q + 1) :=
  ⟨if r ∈ T then q else 0, by split_ifs <;> omega⟩

theorem demand_outside {q : ℕ} (H T : Finset V) (hT : T ⊆ H) :
    ∀ r, r ∉ H → (demand (q := q) T r).val = 0 := by
  intro r hr
  exact if_neg (fun h => hr (hT h))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem exists_benchmark (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I J : Finset (OwnerTasks.Low D Q)) (k : ℕ) (hsize : I.card ≤ k)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val)
    (ξ : ℝ) (hξ : 0 < ξ) :
    let H := PhysicalTasks.vertices G D R L Q I
    let T := OwnerTasks.demands G D R L Q I J
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    ∃ p : V → ℕ, (∑ v, p v) ≤ M ∧ (∀ v, v ∉ H → p v = 0) ∧
      (∀ r, (demand (q := q) T r).val ≤ ∑ v ∈ closed G r, p v) ∧
      (IntegralTable.cost (fun v => (c v).val) p : ℝ) / q ≤
        (1 + ξ) * TaskOptimum.number G D R L Q I J (fun v => ((c v).val : ℝ)) := by
  classical
  dsimp only
  let H := PhysicalTasks.vertices G D R L Q I
  let T := OwnerTasks.demands G D R L Q I J
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  have hcR : ∀ v, (1 : ℝ) ≤ (c v).val := fun v => Nat.one_le_cast.mpr (hc v)
  have hcB : ∀ v, ((c v).val : ℝ) ≤ B := by
    intro v
    exact_mod_cast (by have h := (c v).isLt; omega : (c v).val ≤ B)
  obtain ⟨p, hp, hfeas, hcost, _⟩ := TaskSolverMath.solve G D R L Q I J k hsize a ha hden
    (fun v => ((c v).val : ℝ)) hcR B (Nat.cast_nonneg B) hcB ξ hξ
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hp
  have hv := best_sound (G.induce (H : Set V)) (a : ℝ) (fun v => ((c v.val).val : ℝ)) M
    (LocalFractional.demand (InducedSubsets.lift H T) q) p hp
  refine ⟨NatExtension.extend H p, ?_, NatExtension.outside H p, ?_, ?_⟩
  · rw [NatExtension.sum]
    exact hv.1
  · intro r
    change (if r ∈ T then q else 0) ≤ ∑ v ∈ closed G r, NatExtension.extend H p v
    by_cases hr : r ∈ T
    · let rr : ↥(H : Set V) := ⟨r, PhysicalTasks.demands_subset G D R L Q I J hr⟩
      have hh := hv.2 rr
      have hrr : rr ∈ InducedSubsets.lift H T := Finset.mem_subtype.mpr hr
      simp only [LocalFractional.demand, if_pos hrr] at hh
      rw [if_pos hr]
      change q ≤ ∑ v ∈ closed G rr.val, NatExtension.extend H p v
      rw [NatExtension.closed_sum]
      exact hh
    · rw [if_neg hr]
      exact Nat.zero_le _
  · rw [NatExtension.weighted]
    have he : (IntegralTable.cost (fun v : ↥(H : Set V) => (c v.val).val) p : ℝ) / q =
        PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) (LocalFractional.vector q p) := by
      simp [IntegralTable.cost, PartialOptimum.objective, LocalFractional.vector, mul_div_assoc, Finset.sum_div]
    rw [he]
    exact hcost
end Paper.TaskBenchmark
