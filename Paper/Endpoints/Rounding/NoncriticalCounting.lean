import Paper.Endpoints.Rounding.NoncriticalGeometry

namespace Paper.NoncriticalCounting
open SevenFoundation NoncriticalGeometry
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

noncomputable def overlap : Finset V := high G k σ x ∩ residual G k σ x
noncomputable def outside : Finset V := high G k σ x \ residual G k σ x
noncomputable def middle : Finset V :=
  (residual G k σ x ∩ covered G (high G k σ x)) \ high G k σ x

theorem high_middle_disjoint : Disjoint (high G k σ x) (middle G k σ x) := by
  classical
  exact Finset.disjoint_left.mpr (fun v hv hm => (Finset.mem_sdiff.mp hm).2 hv)

theorem covered_inter_high :
    high G k σ x ∩ (residual G k σ x ∩ covered G (high G k σ x)) = overlap G k σ x := by
  classical
  ext v
  simp only [Finset.mem_inter, overlap]
  constructor
  · rintro ⟨hh, hr, _⟩
    exact ⟨hh, hr⟩
  · rintro ⟨hh, hr⟩
    exact ⟨hh, hr, subset_covered G _ hh⟩

theorem covered_union_high :
    high G k σ x ∪ (residual G k σ x ∩ covered G (high G k σ x)) =
      high G k σ x ∪ middle G k σ x := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, middle, Finset.mem_sdiff]
  tauto

theorem high_card_split :
    (high G k σ x).card = (overlap G k σ x).card + (outside G k σ x).card := by
  have h := Finset.card_sdiff_add_card_inter (high G k σ x) (residual G k σ x)
  change (outside G k σ x).card + (overlap G k σ x).card = (high G k σ x).card at h
  omega

theorem residual_card_split :
    (residual G k σ x).card =
      (overlap G k σ x).card + (middle G k σ x).card + (last G k σ x).card := by
  classical
  have h1 := Finset.card_sdiff_add_card_inter (residual G k σ x) (covered G (high G k σ x))
  have h2 := Finset.card_sdiff_add_card_inter
    (residual G k σ x ∩ covered G (high G k σ x)) (high G k σ x)
  have hi : (residual G k σ x ∩ covered G (high G k σ x)) ∩ high G k σ x =
      overlap G k σ x := by
    rw [Finset.inter_comm]
    exact covered_inter_high G k σ x
  rw [hi] at h2
  change (last G k σ x).card + _ = _ at h1
  change (middle G k σ x).card + _ = _ at h2
  omega

theorem output_card_split :
    (output G k σ x).card =
      (first G k σ x).card + (high G k σ x).card + (last G k σ x).card := by
  classical
  have hwU : Disjoint (first G k σ x) (last G k σ x) := by
    apply Finset.disjoint_left.mpr
    intro v hw hu
    exact Finset.disjoint_left.mp (residual_disjoint_first G k σ x)
      (last_subset_residual G k σ x hu) hw
  have hhU := (last_disjoint_high G k σ x).symm
  have hwH := (high_disjoint_first G k σ x).symm
  unfold NoncriticalGeometry.output
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hwU, hhU⟩),
    Finset.card_union_of_disjoint hwH]

theorem output_card_identity :
    ((output G k σ x).card : ℝ) = (first G k σ x).card +
      (residual G k σ x).card - (middle G k σ x).card + (outside G k σ x).card := by
  have h1 := high_card_split G k σ x
  have h2 := residual_card_split G k σ x
  have h3 := output_card_split G k σ x
  have hnat : (output G k σ x).card + (middle G k σ x).card =
      (first G k σ x).card + (residual G k σ x).card + (outside G k σ x).card := by omega
  have hr : ((output G k σ x).card : ℝ) + (middle G k σ x).card =
      (first G k σ x).card + (residual G k σ x).card + (outside G k σ x).card := by
    exact_mod_cast hnat
  linarith


end Paper.NoncriticalCounting
