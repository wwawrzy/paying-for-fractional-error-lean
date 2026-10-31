import Paper.Endpoints.Rounding.NoncriticalExcess

namespace Paper.NoncriticalMass
open SevenFoundation NoncriticalGeometry NoncriticalCounting NoncriticalExcess
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

noncomputable def slack (a : ℝ) : ℝ :=
  ∑ v ∈ low G k σ x, ((2 * a + 1) - (hits G k σ x v : ℝ)) * x v

theorem low_coefficient (a θ : ℝ) (heq : 2 * a = k + θ) {v : V} (hv : v ∈ low G k σ x) :
    θ ≤ (2 * a + 1) - (hits G k σ x v : ℝ) := by
  have hh : (hits G k σ x v : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Finset.mem_filter.mp hv).2
  push_cast at hh
  linarith

theorem high_low_disjoint : Disjoint (high G k σ x) (low G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hh hl
  have h1 := (Finset.mem_filter.mp hh).2
  have h2 := (Finset.mem_filter.mp hl).2
  omega

theorem low_not_first {v : V} (hv : v ∈ low G k σ x) : v ∉ first G k σ x :=
  (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2

theorem low_of_not {v : V} (hw : v ∉ first G k σ x) (hh : v ∉ high G k σ x) : v ∈ low G k σ x := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩
  have hn : ¬ k + 2 ≤ hits G k σ x v := fun h =>
    hh (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, h⟩)
  omega

theorem sum_partition : (∑ v, x v) =
    (∑ v ∈ first G k σ x, x v) + (∑ v ∈ high G k σ x, x v) + (∑ v ∈ low G k σ x, x v) := by
  have he : ∀ v, x v = (if v ∈ first G k σ x then x v else 0) +
      (if v ∈ high G k σ x then x v else 0) + (if v ∈ low G k σ x then x v else 0) := by
    intro v
    by_cases hw : v ∈ first G k σ x
    · have hh : v ∉ high G k σ x := fun h => Finset.disjoint_left.mp (high_disjoint_first G k σ x) h hw
      have hl : v ∉ low G k σ x := fun h => low_not_first G k σ x h hw
      simp only [if_pos hw, if_neg hh, if_neg hl, add_zero]
    · by_cases hh : v ∈ high G k σ x
      · have hl : v ∉ low G k σ x := fun h => Finset.disjoint_left.mp (high_low_disjoint G k σ x) hh h
        simp only [if_neg hw, if_pos hh, if_neg hl, zero_add, add_zero]
      · simp only [if_neg hw, if_neg hh, if_pos (low_of_not G k σ x hw hh), zero_add]
  calc
    _ = ∑ v, ((if v ∈ first G k σ x then x v else 0) +
      (if v ∈ high G k σ x then x v else 0) + (if v ∈ low G k σ x then x v else 0)) :=
      Finset.sum_congr rfl (fun v _ => he v)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem low_mass (a θ : ℝ) (heq : 2 * a = k + θ) (hx : ∀ v, 0 ≤ x v) :
    θ * (∑ v ∈ low G k σ x, x v) ≤ slack G k σ x a := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (low_coefficient G k σ x a θ heq hv) (hx v))

theorem mass_bound (a θ : ℝ) (heq : 2 * a = k + θ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hden : Incidence.InducedDensityBound G a)
    (hx : ∀ v, 0 ≤ x v) (hcap : ∀ v, x v ≤ 1) :
    (∑ v, x v) ≤ (first G k σ x).card + σ * a / (1 - θ) * (middle G k σ x).card -
      σ * (a + 1) / (1 - θ) * (outside G k σ x).card + slack G k σ x a / θ := by
  have hw : (∑ v ∈ first G k σ x, x v) ≤ (first G k σ x).card := by
    calc
      _ ≤ ∑ _v ∈ first G k σ x, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hcap v)
      _ = _ := by simp
  have hh : (∑ v ∈ high G k σ x, x v) ≤ σ * (high G k σ x).card := by
    calc
      _ ≤ ∑ _v ∈ high G k σ x, σ := Finset.sum_le_sum (fun _ hv => high_weight G k σ x hv)
      _ = _ := by simp [mul_comm]
  have hi := excess_le G k σ x a hden
  have hlower := excess_lower G k σ x a θ heq
  have hhcard : ((high G k σ x).card : ℝ) ≤
      (a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card) / (1 - θ) :=
    (le_div_iff₀ (by linarith)).mpr (by nlinarith)
  have hl := (le_div_iff₀ hθ).mpr (by simpa only [mul_comm] using low_mass G k σ x a θ heq hx)
  rw [sum_partition G k σ x]
  calc
    _ ≤ (first G k σ x).card + σ *
      ((a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card) / (1 - θ)) +
      slack G k σ x a / θ :=
      add_le_add (add_le_add hw (hh.trans (mul_le_mul_of_nonneg_left hhcard hσ))) hl
    _ = _ := by ring

end Paper.NoncriticalMass
