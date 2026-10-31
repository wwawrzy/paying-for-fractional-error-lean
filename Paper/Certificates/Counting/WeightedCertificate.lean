import Paper.Certificates.Counting.FloatingRound
import Paper.Preliminaries.WeightedIntegrality

/-! Actual weighted multicover certificates with cost at most (q+2a) times a
feasible fractional vector. Paper label: lem:certificate. -/
namespace Paper.WeightedCertificate
attribute [local instance] Classical.propDecidable
open SevenFoundation OrientedNeighborhoods
open FloatingCore
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem incoming_column_cap {a : ℕ} (O : HallOrientation.Orientation G a) (v : V) :
    (Finset.univ.filter (fun r => v ∈ incoming G O r)).card ≤ a := by
  have heq : Finset.univ.filter (fun r => v ∈ incoming G O r) = outgoing G O v := by
    ext r
    simp only [incoming, outgoing, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact outgoing_card_le G O v

theorem closed_loss_lt {a : ℕ} (O : HallOrientation.Orientation G a) (ha : 1 ≤ a)
    (y z : V → ℝ) (hz : ∀ v, 0 ≤ z v)
    (hfixed : ∀ v ∉ floating y, z v = y v)
    (hrows : ∀ r, (∑ v ∈ incoming G O r, y v) - (∑ v ∈ incoming G O r, z v) < a)
    (r : V) : (∑ v ∈ closed G r, y v) - (∑ v ∈ closed G r, z v) < 2 * (a : ℝ) + 1 := by
  have hsub := WeightedIntegrality.incoming_subset_closed G O r
  have hsmall : ((closed G r \ incoming G O r) ∩ floating y).card ≤ a + 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (nonincoming_card_le G O r)
  have hout := FloatingRound.small_row_loss (closed G r \ incoming G O r) (a + 1)
    (by omega) y z hsmall hz hfixed
  have hy := Finset.sum_sdiff (s₁ := incoming G O r) (s₂ := closed G r) (f := y) hsub
  have hz' := Finset.sum_sdiff (s₁ := incoming G O r) (s₂ := closed G r) (f := z) hsub
  have hi := hrows r
  push_cast at hout
  linarith

/-- No optimum vector or solver is postulated: an actual finite integer
multicover is obtained from any given feasible nonnegative vector. -/
theorem exists_certificate (R : Finset V) {a : ℕ} (O : HallOrientation.Orientation G a)
    (ha : 1 ≤ a) (q : ℕ) (c x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v) :
    ∃ m : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ closed G r, m v) ∧
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
  obtain ⟨z, hzint, hzfix, hcost, hrows⟩ := FloatingRound.round (incoming G O) a ha c y hy
    (incoming_column_cap G O)
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
    have hloss := closed_loss_lt G O ha y z hznonneg hzfix hrows r
    have hcov := mul_le_mul_of_nonneg_left (hcover r hr) hp
    have hscale : (∑ v ∈ closed G r, h * x v) = h * ∑ v ∈ closed G r, x v :=
      (Finset.mul_sum _ _ _).symm
    have heq : (∑ v ∈ closed G r, (m v : ℝ)) =
        (∑ v ∈ closed G r, h * x v) - (∑ v ∈ closed G r, y v) +
          ∑ v ∈ closed G r, z v := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [hm]
      dsimp [y]
      ring
    have hreal : (q : ℝ) - 1 < ∑ v ∈ closed G r, (m v : ℝ) := by
      rw [hscale] at heq
      dsimp [h] at heq hcov
      nlinarith
    have hnat : q < (∑ v ∈ closed G r, m v) + 1 := by
      exact_mod_cast (by push_cast; linarith : (q : ℝ) < (∑ v ∈ closed G r, (m v : ℝ)) + 1)
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
end Paper.WeightedCertificate
