import Paper.Certificates.Counting.PartialOptimum

/-! Finite sums of nonnegative physical vectors and repair indicators.
These elementary linear identities are used for the actual outcome. -/
namespace Paper.CoverVectorSum
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V]

noncomputable def vector (F : Finset I) (x : I → V → ℝ) (v : V) : ℝ := ∑ i ∈ F, x i v

theorem nonneg (F : Finset I) (x : I → V → ℝ) (hx : ∀ i ∈ F, ∀ v, 0 ≤ x i v) :
    ∀ v, 0 ≤ vector F x v := fun v => Finset.sum_nonneg (fun i hi => hx i hi v)

theorem single_le (F : Finset I) (x : I → V → ℝ) (hx : ∀ i ∈ F, ∀ v, 0 ≤ x i v)
    {i : I} (hi : i ∈ F) (v : V) : x i v ≤ vector F x v :=
  Finset.single_le_sum (fun j hj => hx j hj v) hi

theorem cost (F : Finset I) (x : I → V → ℝ) (c : V → ℝ) :
    PartialOptimum.objective c (vector F x) = ∑ i ∈ F, PartialOptimum.objective c (x i) := by
  unfold PartialOptimum.objective vector
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem indicator_nonneg (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_covers (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {r : V} (hr : r ∈ covered G S) : 1 ≤ ∑ v ∈ closed G r, indicator S v := by
  obtain ⟨v, hvS, hrv⟩ := Finset.mem_biUnion.mp hr
  have hvr := (closed_symm G r v).mp hrv
  have hs := Finset.single_le_sum (fun u (_ : u ∈ closed G r) => indicator_nonneg S u) hvr
  simpa only [indicator, if_pos hvS] using hs

theorem indicator_cost (S : Finset V) (c : V → ℝ) :
    PartialOptimum.objective c (indicator S) = ∑ v ∈ S, c v := by
  classical
  unfold PartialOptimum.objective indicator
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem indicator_bound (S : Finset V) (c : V → ℝ) (B : ℝ) (hc : ∀ v, c v ≤ B) :
    PartialOptimum.objective c (indicator S) ≤ B * S.card := by
  rw [indicator_cost]
  calc
    _ ≤ ∑ _v ∈ S, B := Finset.sum_le_sum (fun v _ => hc v)
    _ = _ := by simp [mul_comm]

theorem cost_add (c x y : V → ℝ) : PartialOptimum.objective c (fun v => x v + y v) =
    PartialOptimum.objective c x + PartialOptimum.objective c y := by
  simp only [PartialOptimum.objective, mul_add, Finset.sum_add_distrib]
end Paper.CoverVectorSum
