import Paper.Certificates.Counting.WeightedCertificate
import Paper.Certificates.Counting.CoveringOptimum

/-! Multicover certificates for arbitrary local covering sets. -/
namespace Paper.CoveringCertificate
attribute [local instance] Classical.propDecidable
open SevenFoundation OrientedNeighborhoods FloatingCore
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def rows {a : ℕ} (O : HallOrientation.Orientation G a) (C : V → Finset V)
    (r : V) : Finset V := C r ∩ incoming G O r

theorem column_cap {a : ℕ} (O : HallOrientation.Orientation G a)
    (C : V → Finset V) (v : V) :
    (Finset.univ.filter (fun r => v ∈ rows G O C r)).card ≤ a := by
  apply le_trans (Finset.card_le_card ?_) (WeightedCertificate.incoming_column_cap G O v)
  intro r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_inter.mp (Finset.mem_filter.mp hr).2).2⟩

theorem cover_loss_lt {a : ℕ} (O : HallOrientation.Orientation G a)
    (C : V → Finset V) (hC : ∀ r, C r ⊆ closed G r) (ha : 1 ≤ a)
    (y z : V → ℝ) (hz : ∀ v, 0 ≤ z v)
    (hfixed : ∀ v ∉ floating y, z v = y v)
    (hrows : ∀ r, (∑ v ∈ rows G O C r, y v) -
      (∑ v ∈ rows G O C r, z v) < a) (r : V) :
    (∑ v ∈ C r, y v) - (∑ v ∈ C r, z v) < 2 * (a : ℝ) + 1 := by
  have hsub : rows G O C r ⊆ C r := Finset.inter_subset_left
  have houtsub : C r \ rows G O C r ⊆ closed G r \ incoming G O r := by
    intro v hv
    have hmem := Finset.mem_sdiff.mp hv
    refine Finset.mem_sdiff.mpr ⟨hC r hmem.1, ?_⟩
    intro hin
    exact hmem.2 (Finset.mem_inter.mpr ⟨hmem.1, hin⟩)
  have hsmall : ((C r \ rows G O C r) ∩ floating y).card ≤ a + 1 :=
    (Finset.card_le_card (Finset.inter_subset_left.trans houtsub)).trans
      (nonincoming_card_le G O r)
  have hout := FloatingRound.small_row_loss (C r \ rows G O C r) (a + 1)
    (by omega) y z hsmall hz hfixed
  have hy := Finset.sum_sdiff (s₁ := rows G O C r) (s₂ := C r) (f := y) hsub
  have hz' := Finset.sum_sdiff (s₁ := rows G O C r) (s₂ := C r) (f := z) hsub
  have hi := hrows r
  push_cast at hout
  linarith

/-- No optimum vector or solver is postulated: an actual finite integer
multicover is obtained from any given feasible nonnegative vector. -/
theorem exists_certificate (C : V → Finset V)
    (hC : ∀ r, C r ⊆ closed G r) (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (ha : 1 ≤ a) (q : ℕ) (c x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v) :
    ∃ m : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ C r, m v) ∧
      (∑ v, c v * (m v : ℝ)) ≤ (q + 2 * (a : ℝ)) * ∑ v, c v * x v := by
  classical
  let h : ℝ := q + 2 * (a : ℝ)
  let n : V → ℕ := fun v => ⌊h * x v⌋₊
  let y : V → ℝ := fun v => h * x v - n v
  have hp : 0 ≤ h := by dsimp [h]; positivity
  have hy : ∀ v, 0 ≤ y v ∧ y v ≤ 1 := by
    intro v
    have hfloor := Nat.floor_le (mul_nonneg hp (hx v))
    have hlt := Nat.lt_floor_add_one (h * x v)
    constructor <;> dsimp [y, n] <;> linarith
  obtain ⟨z, hzint, hzfix, hcost, hrows⟩ := FloatingRound.round (rows G O C) a ha c y hy
    (column_cap G O C)
  let b : V → ℕ := fun v => if z v = 1 then 1 else 0
  have hb : ∀ v, (b v : ℝ) = z v := by
    intro v
    rcases hzint v with hv | hv
    · simp [b, hv]
    · simp [b, hv]
  let m : V → ℕ := fun v => n v + b v
  have hm : ∀ v, (m v : ℝ) = (n v : ℝ) + z v := by
    intro v
    dsimp [m]
    rw [Nat.cast_add, hb]
  have hznonneg : ∀ v, 0 ≤ z v := by
    intro v
    rcases hzint v with hv | hv <;> rw [hv] <;> norm_num
  refine ⟨m, ?_, ?_⟩
  · intro r hr
    have hloss := cover_loss_lt G O C hC ha y z hznonneg hzfix hrows r
    have hcov := mul_le_mul_of_nonneg_left (hcover r hr) hp
    have hscale : (∑ v ∈ C r, h * x v) = h * ∑ v ∈ C r, x v :=
      (Finset.mul_sum _ _ _).symm
    have heq : (∑ v ∈ C r, (m v : ℝ)) =
        (∑ v ∈ C r, h * x v) - (∑ v ∈ C r, y v) +
          ∑ v ∈ C r, z v := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [hm]
      dsimp [y]
      ring
    have hreal : (q : ℝ) - 1 < ∑ v ∈ C r, (m v : ℝ) := by
      rw [hscale] at heq
      dsimp [h] at heq hcov
      nlinarith
    have hnat : q < (∑ v ∈ C r, m v) + 1 := by
      exact_mod_cast (by push_cast; linarith : (q : ℝ) < (∑ v ∈ C r, (m v : ℝ)) + 1)
    omega
  · have heq : (∑ v, c v * (m v : ℝ)) = (∑ v, c v * (n v : ℝ)) + ∑ v, c v * z v := by
      simp_rw [hm, mul_add]
      rw [Finset.sum_add_distrib]
    have heq' : (∑ v, c v * (n v : ℝ)) + ∑ v, c v * y v = h * ∑ v, c v * x v := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [y]
      ring
    rw [heq]
    dsimp [h] at heq'
    linarith

/-- Positive unit lower bounds on costs also bound the number of copies. -/
theorem copies_le_cost (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (m : V → ℕ) :
    (∑ v, (m v : ℝ)) ≤ ∑ v, c v * (m v : ℝ) := by
  apply Finset.sum_le_sum
  intro v _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc v) (Nat.cast_nonneg (m v))
end Paper.CoveringCertificate
