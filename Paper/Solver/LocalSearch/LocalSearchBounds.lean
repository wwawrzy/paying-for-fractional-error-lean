import Paper.Certificates.Counting.WeightedCertificate
import Paper.Endpoints.Rounding.WeightedBudget

/-! Graph-level branching bounds for the bounded-certificate local search. -/
namespace Paper.LocalSearchBounds
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def heavy (A : Finset V) (m : ℕ) : Finset V :=
  Finset.univ.filter (fun v => A.card ≤ m * (closed G v ∩ A).card)

theorem incidence_le (A C : Finset V) {t : ℝ} (hden : Incidence.InducedDensityBound G t) :
    (∑ v ∈ C, ((closed G v ∩ A).card : ℝ)) ≤ t * A.card + (t + 1) * C.card := by
  have h := Incidence.closed_incidence_le_of_density G hden C A
  have hc : ((C ∪ A).card : ℝ) + (C ∩ A).card = C.card + A.card := by
    exact_mod_cast Finset.card_union_add_card_inter C A
  have hi : ((C ∩ A).card : ℝ) ≤ C.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : C ∩ A ⊆ C)
  have hmul := congrArg (fun z : ℝ => t * z) hc
  nlinarith only [h, hi, hmul]

theorem heavy_card_le (A : Finset V) (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 1 ≤ t)
    (hden : Incidence.InducedDensityBound G t)
    (hlarge : 2 * (t + 1) * m ≤ (A.card : ℝ)) :
    ((heavy G A m).card : ℝ) ≤ 2 * t * m := by
  let C := heavy G A m
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hAp : (0 : ℝ) < A.card := by nlinarith
  have hlow : (C.card : ℝ) * A.card ≤
      (m : ℝ) * ∑ v ∈ C, ((closed G v ∩ A).card : ℝ) := by
    calc
      _ = ∑ _v ∈ C, (A.card : ℝ) := by simp
      _ ≤ ∑ v ∈ C, (m : ℝ) * ((closed G v ∩ A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast (Finset.mem_filter.mp hv).2
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hu := mul_le_mul_of_nonneg_left (incidence_le G A C hden) hmp.le
  have hbig := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg C.card)
  have hfinal : (C.card : ℝ) * A.card ≤ (2 * t * m) * A.card := by
    nlinarith only [hlow, hu, hbig]
  exact (mul_le_mul_iff_left₀ hAp).mp hfinal

/-- Every completion with at most m copies contains an actually heavy candidate.
This is the completeness reason for branching on the bounded heavy list. -/
theorem completion_hits_heavy (A : Finset V) (hA : A.Nonempty) (m : ℕ) (hm : 1 ≤ m)
    (p : V → ℕ) (hsize : ∑ v, p v ≤ m)
    (hcover : ∀ r ∈ A, 1 ≤ ∑ v ∈ closed G r, p v) :
    ∃ v ∈ heavy G A m, 0 < p v := by
  classical
  by_contra hn
  push Not at hn
  have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcover' : (A.card : ℝ) ≤ ∑ v, ((closed G v ∩ A).card : ℝ) * (p v : ℝ) := by
    rw [← WeightedBudget.incidence_sum G A (fun v => (p v : ℝ))]
    calc
      _ = ∑ _r ∈ A, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun r hr => by exact_mod_cast hcover r hr)
  have hpoint : ∀ v, (m : ℝ) * ((closed G v ∩ A).card : ℝ) * (p v : ℝ) ≤
      ((A.card : ℝ) - 1) * (p v : ℝ) := by
    intro v
    by_cases hp : p v = 0
    · simp only [hp, Nat.cast_zero, mul_zero, le_refl]
    have hv : v ∉ heavy G A m := by
      intro hv
      have h := hn v hv
      omega
    have hlt : m * (closed G v ∩ A).card + 1 ≤ A.card := by
      have hn' : ¬ A.card ≤ m * (closed G v ∩ A).card := by
        intro h
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    have hr : (m : ℝ) * ((closed G v ∩ A).card : ℝ) + 1 ≤ A.card := by exact_mod_cast hlt
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg (p v))
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hpoint v)
  simp only [mul_assoc, ← Finset.mul_sum] at hsum
  have hsize' : (∑ v, (p v : ℝ)) ≤ m := by exact_mod_cast hsize
  have hu := mul_le_mul_of_nonneg_left hsize' (by linarith : 0 ≤ (A.card : ℝ) - 1)
  have hl := mul_le_mul_of_nonneg_left hcover' hmp.le
  nlinarith
end Paper.LocalSearchBounds
