import Paper.Endpoints.Rounding.ImprovedExcessGeometry

/-! Graph incidence, excess, cost saving and mass for the exact unfiltered
rule. Each of the two induced-edge terms contributes one copy of eta. -/
namespace Paper.ImprovedExcess
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def DensityWithExcess (a η : ℝ) : Prop :=
  ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ a * S.card + η

theorem incidence_bound (a η : ℝ) (hden : DensityWithExcess G a η) (A B : Finset V) :
    (∑ v ∈ A, ((closed G v ∩ B).card : ℝ)) ≤
      a * (A ∪ B).card + (a + 1) * (A ∩ B).card + 2 * η := by
  have hnat := Incidence.closed_incidence_le G A B
  have hreal : (∑ v ∈ A, ((closed G v ∩ B).card : ℝ)) ≤
      (G.inducedEdgeCount (A ∪ B) : ℝ) +
        (G.inducedEdgeCount (A ∩ B) : ℝ) + (A ∩ B).card := by
    exact_mod_cast hnat
  have hu := hden (A ∪ B)
  have hi := hden (A ∩ B)
  linarith

variable (k : ℕ) (σ : ℝ) (x : V → ℝ)

theorem excess_le (a η : ℝ) (hden : DensityWithExcess G a η) :
    excess G k σ x a ≤
      a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card + 2 * η := by
  classical
  have hinc := incidence_bound G a η hden
    (high G k σ x) (residual G k σ x ∩ covered G (high G k σ x))
  have hsum : (∑ v ∈ high G k σ x,
      ((closed G v ∩ (residual G k σ x ∩ covered G (high G k σ x))).card : ℝ)) =
      ∑ v ∈ high G k σ x, (hits G k σ x v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have heq : closed G v ∩ (residual G k σ x ∩ covered G (high G k σ x)) =
        closed G v ∩ residual G k σ x := by
      ext r
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hc, hr, _⟩
        exact ⟨hc, hr⟩
      · rintro ⟨hc, hr⟩
        exact ⟨hc, hr, Finset.mem_biUnion.mpr ⟨v, hv, hc⟩⟩
    rw [heq]
    rfl
  rw [hsum, covered_inter_high, covered_union_high,
    Finset.card_union_of_disjoint (high_middle_disjoint G k σ x)] at hinc
  have hcard : ((high G k σ x).card : ℝ) =
      (overlap G k σ x).card + (outside G k σ x).card := by
    exact_mod_cast high_card_split G k σ x
  have he : excess G k σ x a = (∑ v ∈ high G k σ x, (hits G k σ x v : ℝ)) -
      (2 * a + 1 : ℝ) * (high G k σ x).card := by
    simp [excess, Finset.sum_sub_distrib, mul_comm]
    ring
  push_cast at hinc he
  rw [hcard] at he hinc
  rw [he]
  nlinarith

theorem high_card_bound (a θ η : ℝ) (heq : 2 * a = k + θ)
    (hden : DensityWithExcess G a η) :
    (1 - θ) * (high G k σ x).card ≤
      a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card + 2 * η :=
  (excess_lower G k σ x a θ heq).trans (excess_le G k σ x a η hden)

theorem slack_nonneg (a θ : ℝ) (heq : 2 * a = k + θ) (hθ : 0 < θ)
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ slack G k σ x a := by
  have hp := low_mass G k σ x a θ heq hx
  have hsum : 0 ≤ ∑ v ∈ low G k σ x, x v := Finset.sum_nonneg fun v _ => hx v
  exact (mul_nonneg hθ.le hsum).trans hp

theorem saving (a θ η : ℝ) (ha : 0 ≤ a) (heq : 2 * a = k + θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hden : DensityWithExcess G a η)
    (hx : PartialOptimum.Feasible G Finset.univ x) :
    ((2 * a + 1) * σ - 1) * (first G k σ x).card +
      (1 - a * σ) * (middle G k σ x).card +
      ((a + 1) * σ - 1) * (outside G k σ x).card + slack G k σ x a - 2 * η * σ ≤
        (2 * a + 1) * (∑ v, x v) - (output G k σ x).card := by
  have hw := mul_le_mul_of_nonneg_left (first_mass_lower G k σ x)
    (show (0 : ℝ) ≤ 2 * a + 1 by linarith)
  have hr := residual_coverage G k σ x hx
  have he := weighted_excess G k σ x a θ heq hθ1
  have hi := mul_le_mul_of_nonneg_left (excess_le G k σ x a η hden) hσ
  have hc := cost_decomposition G k σ x a
  have hcard := output_card_identity G k σ x
  nlinarith

theorem mass_bound (a θ η : ℝ) (heq : 2 * a = k + θ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hden : DensityWithExcess G a η)
    (hx : ∀ v, 0 ≤ x v) (hcap : ∀ v, x v ≤ 1) :
    (∑ v, x v) ≤ (first G k σ x).card + σ * a / (1 - θ) * (middle G k σ x).card -
      σ * (a + 1) / (1 - θ) * (outside G k σ x).card + slack G k σ x a / θ +
      2 * η * σ / (1 - θ) := by
  have hw : (∑ v ∈ first G k σ x, x v) ≤ (first G k σ x).card := by
    calc
      _ ≤ ∑ _v ∈ first G k σ x, (1 : ℝ) := Finset.sum_le_sum fun v _ => hcap v
      _ = _ := by simp
  have hh : (∑ v ∈ high G k σ x, x v) ≤ σ * (high G k σ x).card := by
    calc
      _ ≤ ∑ _v ∈ high G k σ x, σ := Finset.sum_le_sum fun _ hv => high_weight G k σ x hv
      _ = _ := by simp [mul_comm]
  have hH := high_card_bound G k σ x a θ η heq hden
  have hhcard : ((high G k σ x).card : ℝ) ≤
      (a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card + 2 * η) / (1 - θ) :=
    (le_div_iff₀ (by linarith)).mpr (by simpa only [mul_comm] using hH)
  have hl := (le_div_iff₀ hθ).mpr (by simpa only [mul_comm] using low_mass G k σ x a θ heq hx)
  rw [sum_partition G k σ x]
  calc
    _ ≤ (first G k σ x).card + σ *
      ((a * (middle G k σ x).card - (a + 1) * (outside G k σ x).card + 2 * η) / (1 - θ)) +
      slack G k σ x a / θ :=
      add_le_add (add_le_add hw (hh.trans (mul_le_mul_of_nonneg_left hhcard hσ))) hl
    _ = _ := by ring

end Paper.ImprovedExcess
#print axioms Paper.ImprovedExcess.incidence_bound
#print axioms Paper.ImprovedExcess.excess_le
#print axioms Paper.ImprovedExcess.saving
#print axioms Paper.ImprovedExcess.mass_bound
