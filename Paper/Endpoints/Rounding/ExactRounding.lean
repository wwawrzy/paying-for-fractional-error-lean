import Paper.Preliminaries.DefectZone

/-! Exact critical-degree rounding from a feasible approximate auxiliary vector.
The fractional solver and its broadcast implementation remain separate obligations. -/
namespace Paper.ExactRounding
attribute [local instance] Classical.propDecidable
open SevenFoundation
open WeightedBudget (auxiliary zone boundaryCost initialDemands auxiliaryNumber)
open SelectionGeometry SelectionSaving
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (t : ℝ) (x : V → ℝ)

/-- The selected centers together with the residual demands give a feasible
integral comparison for the auxiliary LP. -/
theorem comparison_feasible :
    feasible (auxiliary G d) (indicator (first G d t x ∪ residual G d t x)) := by
  classical
  let S := first G d t x ∪ residual G d t x
  have hS : S ⊆ zone G d := Finset.union_subset
    (first_subset_zone G d t x) (residual_subset_zone G d t x)
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp only [indicator]
    split_ifs <;> norm_num
  · intro v hv
    change v ∉ zone G d at hv
    have hn : v ∉ S := fun hs => hv (hS hs)
    exact if_neg hn
  · intro r hr
    change r ∈ initialDemands G d at hr
    have hex : ∃ v ∈ S, v ∈ closed G r ∩ zone G d := by
      by_cases hw : r ∈ covered G (first G d t x)
      · obtain ⟨v, hv, hrv⟩ := Finset.mem_biUnion.mp hw
        exact ⟨v, Finset.mem_union_left _ hv, Finset.mem_inter.mpr
          ⟨(closed_symm G r v).mp hrv, first_subset_zone G d t x hv⟩⟩
      · have hrR : r ∈ residual G d t x := Finset.mem_sdiff.mpr ⟨hr, hw⟩
        exact ⟨r, Finset.mem_union_right _ hrR,
          Finset.mem_inter.mpr ⟨self_mem_closed G r, residual_subset_zone G d t x hrR⟩⟩
    obtain ⟨v, hvS, hv⟩ := hex
    have hs := Finset.single_le_sum
      (fun i (_ : i ∈ closed G r ∩ zone G d) =>
        show (0 : ℝ) ≤ indicator S i by unfold indicator; split_ifs <;> norm_num) hv
    simpa only [indicator, if_pos hvS] using hs

theorem comparison_cost :
    cost (auxiliary G d) (indicator (first G d t x ∪ residual G d t x)) ≤
      (d + 1 : ℕ) * ((first G d t x).card + (residual G d t x).card) := by
  classical
  let S := first G d t x ∪ residual G d t x
  have hS : S ⊆ zone G d := Finset.union_subset
    (first_subset_zone G d t x) (residual_subset_zone G d t x)
  have heq : cost (auxiliary G d) (indicator S) = ∑ v ∈ S, boundaryCost G d v := by
    unfold cost
    simp only [indicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    have hf : (Finset.univ : Finset V).filter (fun v => v ∈ S) = S := by ext v; simp
    rw [hf]
    simp only [auxiliary]
    apply Finset.sum_congr rfl
    intro v hv
    exact if_pos (hS hv)
  have hb : cost (auxiliary G d) (indicator S) ≤ (d + 1 : ℕ) * S.card := by
    rw [heq]
    calc
      _ ≤ ∑ _v ∈ S, ((d + 1 : ℕ) : ℝ) := Finset.sum_le_sum
        (fun v hv => (WeightedBudget.boundaryCost_bounds G d (hS hv)).2)
      _ = _ := by simp [mul_comm]; ring
  have hc : (S.card : ℝ) ≤ (first G d t x).card + (residual G d t x).card := by
    exact_mod_cast Finset.card_union_le (first G d t x) (residual G d t x)
  exact hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))

theorem optimum_le_comparison :
    auxiliaryNumber G d ≤ (d + 1 : ℕ) *
      ((first G d t x).card + (residual G d t x).card) := by
  have hopt : auxiliaryNumber G d ≤
      cost (auxiliary G d) (indicator (first G d t x ∪ residual G d t x)) := by
    apply csInf_le (WeightedBudget.auxiliaryFeasibleCosts_bddBelow G d)
    exact ⟨_, comparison_feasible G d t x, rfl⟩
  exact hopt.trans (comparison_cost G d t x)

/-- One coefficient controls the auxiliary optimum, as in the current human draft. -/
def kappa (d : ℕ) : ℝ := ((d + 1 : ℕ) : ℝ) ^ 2 * (1 + (d : ℝ) ^ 2)

noncomputable def accuracy (d : ℕ) (t : ℝ) : ℝ := 1 / ((t + 1) * kappa d)

theorem kappa_pos (d : ℕ) : 0 < kappa d := by unfold kappa; positivity

theorem accuracy_pos (d : ℕ) {t : ℝ} (ht : 1 ≤ t) : 0 < accuracy d t := by
  unfold accuracy
  exact one_div_pos.mpr (mul_pos (by linarith) (kappa_pos d))

theorem optimum_control (ht : 1 ≤ t) (hd : (d : ℝ) = 2 * t)
    (hden : MinorDensity.Bound G t) (hx : feasible (auxiliary G d) x) :
    auxiliaryNumber G d ≤ kappa d *
      ((first G d t x).card + (middle G d t x).card + slack G d t x) := by
  let w : ℝ := (first G d t x).card
  let l : ℝ := (middle G d t x).card
  let P := slack G d t x
  let M : ℝ := 1 + (d : ℝ) ^ 2
  let b : ℝ := (d + 1 : ℕ)
  have hw : 0 ≤ w := Nat.cast_nonneg _
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have hp : 0 ≤ P := slack_nonneg G d t x hx.1
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (d : ℝ)]
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hdpos : 1 ≤ d := by
    have hreal : (1 : ℝ) ≤ d := by rw [hd]; linarith
    exact_mod_cast hreal
  have hR := DefectZone.residual_card_le G d t x hden hd hdpos hx
  have hopt := optimum_le_comparison G d t x
  have hMw : w ≤ M * w := by nlinarith
  have hcoeff : t + 1 ≤ b := by dsimp [b]; push_cast; linarith
  have hdcoeff : (d : ℝ) ≤ b := by dsimp [b]; push_cast; linarith
  have hc1 := mul_le_mul_of_nonneg_right hcoeff (add_nonneg hw hl)
  have hc2 := mul_le_mul_of_nonneg_right hdcoeff hp
  have hinside : (t + 1) * (w + l) + d * P ≤ b * (w + l + P) := by
    nlinarith only [hc1, hc2]
  calc
    auxiliaryNumber G d ≤ b * (w + (residual G d t x).card) := hopt
    _ ≤ b * (w + M * (t * w + (t + 1) * l + d * P)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hR) hb
    _ ≤ b * (M * ((t + 1) * (w + l) + d * P)) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hMw]) hb
    _ ≤ b * (M * (b * (w + l + P))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinside (by linarith)) hb
    _ = kappa d * (w + l + P) := by unfold kappa; dsimp [b, M]; ring

theorem saving_lower (ht : 1 ≤ t) (hd : (d : ℝ) = 2 * t)
    (hden : MinorDensity.Bound G t) (hx : feasible (auxiliary G d) x) :
    ((first G d t x).card + (middle G d t x).card + slack G d t x) / (t + 1) ≤
      cost (auxiliary G d) x - (localOutput G d t x).card := by
  have htp : 0 < t + 1 := by linarith
  have hs := selection_saving G d t x ht hd (MinorDensity.induced_bound G hden) hx
  have hw : (0 : ℝ) ≤ (first G d t x).card := Nat.cast_nonneg _
  have hp := slack_nonneg G d t x hx.1
  have hfirst : 1 / (t + 1) * (first G d t x).card ≤
      t / (t + 1) * (first G d t x).card :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ht (le_of_lt htp)) hw
  have hslack : slack G d t x / (t + 1) ≤ slack G d t x := by
    apply (div_le_iff₀ htp).mpr
    nlinarith
  rw [add_div, add_div]
  simp only [one_div_mul_eq_div] at hfirst hs
  linarith

/-- Exact rounding: all graph estimates are proved above. The only algorithmic
input here is a feasible auxiliary vector with the stated solver accuracy. -/
theorem localOutput_le_optimum (ht : 1 ≤ t) (hd : (d : ℝ) = 2 * t)
    (hden : MinorDensity.Bound G t) (hx : feasible (auxiliary G d) x)
    (happrox : cost (auxiliary G d) x ≤ (1 + accuracy d t) * auxiliaryNumber G d) :
    ((localOutput G d t x).card : ℝ) ≤ auxiliaryNumber G d := by
  have htp : 0 < t + 1 := by linarith
  have hk := kappa_pos d
  have hcontrol := optimum_control G d t x ht hd hden hx
  have hsave := saving_lower G d t x ht hd hden hx
  have hpaid : accuracy d t * auxiliaryNumber G d ≤
      ((first G d t x).card + (middle G d t x).card + slack G d t x) / (t + 1) := by
    unfold accuracy
    apply (le_div_iff₀ htp).mpr
    have heq : 1 / ((t + 1) * kappa d) * auxiliaryNumber G d * (t + 1) =
        auxiliaryNumber G d / kappa d := by field_simp
    rw [heq]
    exact (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hcontrol)
  nlinarith

theorem output_bound (ht : 1 ≤ t) (hd : (d : ℝ) = 2 * t)
    (hden : MinorDensity.Bound G t) (hx : feasible (auxiliary G d) x)
    (happrox : cost (auxiliary G d) x ≤ (1 + accuracy d t) * auxiliaryNumber G d) :
    dominates G (output G d t x) ∧
      ((output G d t x).card : ℝ) ≤ (d + 1 : ℕ) * fractionalNumber G := by
  refine ⟨output_dominates G d t x, ?_⟩
  have hlocal := localOutput_le_optimum G d t x ht hd hden hx happrox
  have hbudget := WeightedBudget.fractional_budget G d
  have hcard : ((output G d t x).card : ℝ) ≤
      (WeightedBudget.far G d).card + (localOutput G d t x).card := by
    exact_mod_cast Finset.card_union_le (WeightedBudget.far G d) (localOutput G d t x)
  linarith

end Paper.ExactRounding
