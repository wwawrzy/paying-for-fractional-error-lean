import Paper.Solver.LocalSearch.LocalSearchBounds

/-! Exact compression to minimum-cost coverage masks for the terminal local
search. It applies to genuine graph neighborhoods and integer multiplicities. -/
namespace Paper.MaskCompression
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def masks (A : Finset V) : Finset (Finset V) :=
  Finset.univ.image (fun v => closed G v ∩ A)

theorem masks_card_le (A : Finset V) : (masks G A).card ≤ 2 ^ A.card := by
  have hs : masks G A ⊆ A.powerset := by
    intro S hS
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powerset.mpr Finset.inter_subset_right
  exact (Finset.card_le_card hs).trans_eq (Finset.card_powerset A)

theorem mask_fiber_nonempty (A : Finset V) (S : masks G A) :
    (Finset.univ.filter (fun v => closed G v ∩ A = S.val)).Nonempty := by
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp S.property
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩

noncomputable def representative (A : Finset V) (c : V → ℝ) (S : masks G A) : V :=
  (Finset.exists_min_image (Finset.univ.filter (fun v => closed G v ∩ A = S.val)) c
    (mask_fiber_nonempty G A S)).choose

theorem representative_mask (A : Finset V) (c : V → ℝ) (S : masks G A) :
    closed G (representative G A c S) ∩ A = S.val :=
  (Finset.mem_filter.mp (Finset.exists_min_image
    (Finset.univ.filter (fun v => closed G v ∩ A = S.val)) c
    (mask_fiber_nonempty G A S)).choose_spec.1).2

theorem representative_cost_le (A : Finset V) (c : V → ℝ) (S : masks G A)
    (v : V) (hv : closed G v ∩ A = S.val) : c (representative G A c S) ≤ c v :=
  (Finset.exists_min_image (Finset.univ.filter (fun v => closed G v ∩ A = S.val)) c
    (mask_fiber_nonempty G A S)).choose_spec.2 v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

noncomputable def canonical (A : Finset V) (c : V → ℝ) (v : V) : V :=
  representative G A c ⟨closed G v ∩ A, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩

noncomputable def representatives (A : Finset V) (c : V → ℝ) : Finset V :=
  Finset.univ.image (representative G A c)

theorem representatives_card_le (A : Finset V) (c : V → ℝ) :
    (representatives G A c).card ≤ 2 ^ A.card := by
  exact (Finset.card_image_le).trans (by
    simpa only [Finset.card_univ, Fintype.card_coe] using masks_card_le G A)

/-- Push integer multiplicities through a map; copies at equal representatives
are added rather than discarded. -/
noncomputable def push (f : V → V) (p : V → ℕ) (u : V) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => f v = u), p v

theorem push_sum (f : V → V) (p : V → ℕ) : (∑ u, push f p u) = ∑ v, p v := by
  classical
  simp only [push, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem push_cost (f : V → V) (p : V → ℕ) (c : V → ℝ) :
    (∑ u, c u * (push f p u : ℝ)) = ∑ v, c (f v) * (p v : ℝ) := by
  classical
  simp only [push, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem push_restrict (f : V → V) (p : V → ℕ) (T : Finset V) :
    (∑ u ∈ T, push f p u) = ∑ v, if f v ∈ T then p v else 0 := by
  classical
  simp only [push, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem canonical_covers_iff (A : Finset V) (c : V → ℝ) {r : V} (hr : r ∈ A) (v : V) :
    canonical G A c v ∈ closed G r ↔ v ∈ closed G r := by
  have he := representative_mask G A c
    ⟨closed G v ∩ A, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  have hi := Finset.ext_iff.mp he r
  simp only [Finset.mem_inter, hr, and_true] at hi
  exact (closed_symm G (canonical G A c v) r).trans (hi.trans (closed_symm G r v))

theorem compressed_coverage (A : Finset V) (c : V → ℝ) (p : V → ℕ) {r : V} (hr : r ∈ A) :
    (∑ u ∈ closed G r, push (canonical G A c) p u) = ∑ v ∈ closed G r, p v := by
  rw [push_restrict]
  simp_rw [canonical_covers_iff G A c hr]
  have hf : (Finset.univ : Finset V).filter (fun v => v ∈ closed G r) = closed G r := by
    ext v
    simp
  rw [← Finset.sum_filter, hf]

theorem compressed_cost_le (A : Finset V) (c : V → ℝ) (p : V → ℕ) :
    (∑ u, c u * (push (canonical G A c) p u : ℝ)) ≤ ∑ v, c v * (p v : ℝ) := by
  rw [push_cost]
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_right
    (representative_cost_le G A c _ v rfl) (Nat.cast_nonneg (p v))

theorem compressed_support (A : Finset V) (c : V → ℝ) (p : V → ℕ) {u : V}
    (hu : u ∉ representatives G A c) : push (canonical G A c) p u = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  have heq : canonical G A c v = u := (Finset.mem_filter.mp hv).2
  have hc : canonical G A c v ∈ representatives G A c :=
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  exact False.elim (hu (heq ▸ hc))
end Paper.MaskCompression
