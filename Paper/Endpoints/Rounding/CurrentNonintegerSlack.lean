import Paper.Endpoints.Rounding.CurrentRounding

/-! Exact noninteger branch of the current rounding endpoint.

The hypotheses `2*a = k + theta`, `0 < theta < 1` characterize k as
`floor (2*a)`. This file proves the branch's high/last-set bounds and the
fixed paying slack, reusing the current arbitrary-input rounding lemmas.
-/
namespace Paper.CurrentNonintegerSlack

attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation CurrentRounding
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def uniformInput (a : ℝ) (ha : 1 ≤ a) (x : V → ℝ)
    (hx : feasible (ordinary G) x) (hcap : ∀ v, x v ≤ 1) :
    CurrentRounding.Input G a where
  candidates := Finset.univ
  demands := Finset.univ
  demands_subset := Finset.Subset.rfl
  c := fun _ => 2 * a + 1
  x := x
  cost_pos := by
    intro v hv
    linarith
  cost_le := by
    intro v hv
    rfl
  nonneg := fun v _ => hx.1 v
  cap := fun v _ => hcap v
  coverage := by
    intro r hr
    simpa only [Finset.inter_univ] using hx.2.2 r (Finset.mem_univ _)

variable (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (theta : ℝ)
variable (hdecomp : 2 * a = (k : ℝ) + theta)
variable (htheta0 : 0 < theta) (htheta1 : theta < 1)
variable (hden : Incidence.InducedDensityBound G a)
variable (x : V → ℝ) (hx : feasible (ordinary G) x) (hcap : ∀ v, x v ≤ 1)

local notation "I" => uniformInput G a ha x hx hcap

include G ha k theta hdecomp htheta0 htheta1 hden x hx hcap

theorem high_card_bound :
    ((CurrentRounding.high G a I).card : ℝ) ≤
      a * (CurrentRounding.middle G a I).card / (1 - theta) := by
  have hex := CurrentRounding.excess_le G a I hden
  have hpoint : ∀ v ∈ CurrentRounding.high G a I,
      1 - theta ≤ (CurrentRounding.hits G a I v : ℝ) - (2 * a + 1) := by
    intro v hv
    have hthreshold := (Finset.mem_filter.mp hv).2
    have hnat : k + 2 ≤ CurrentRounding.hits G a I v := by
      by_contra hn
      have hle : CurrentRounding.hits G a I v ≤ k + 1 := by omega
      have hleR : (CurrentRounding.hits G a I v : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast hle
      push_cast at hleR
      rw [hdecomp] at hthreshold
      push_cast at hthreshold
      nlinarith
    have hnatR : (k + 2 : ℕ) ≤ (CurrentRounding.hits G a I v : ℝ) := by
      exact_mod_cast hnat
    push_cast at hnatR
    rw [hdecomp]
    push_cast
    nlinarith
  have hsum := Finset.sum_le_sum (fun v hv => hpoint v hv)
  have hE : (1 - theta) * (CurrentRounding.high G a I).card ≤
      CurrentRounding.excess G a I := by
    unfold CurrentRounding.excess
    calc
      (1 - theta) * (CurrentRounding.high G a I).card =
          ∑ v ∈ CurrentRounding.high G a I, (1 - theta) := by simp; ring
      _ ≤ ∑ v ∈ CurrentRounding.high G a I,
          ((CurrentRounding.hits G a I v : ℝ) - (2 * a + 1)) := hsum
  have hout : (0 : ℝ) ≤ (CurrentRounding.outside G a I).card := Nat.cast_nonneg _
  have hE' : (1 - theta) * (CurrentRounding.high G a I).card ≤
      a * (CurrentRounding.middle G a I).card := by
    have hterm : (0 : ℝ) ≤ (a + 1) * (CurrentRounding.outside G a I).card :=
      mul_nonneg (by linarith) hout
    linarith
  rw [le_div_iff₀ (by linarith : 0 < 1 - theta)]
  nlinarith

theorem other_hit_bound {v : V} (hv : v ∈ CurrentRounding.other G a I) :
    CurrentRounding.hits G a I v ≤ k + 1 := by
  have hnotWH := (Finset.mem_sdiff.mp hv).2
  have hnH : v ∉ CurrentRounding.high G a I :=
    fun hh => hnotWH (Finset.mem_union_right _ hh)
  have hnW : v ∉ CurrentRounding.first G a I :=
    fun hw => hnotWH (Finset.mem_union_left _ hw)
  have hnthreshold : ¬ 2 * a + 1 ≤ (CurrentRounding.hits G a I v : ℝ) := by
    intro hthreshold
    exact hnH (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnW⟩, hthreshold⟩)
  have hlt : (CurrentRounding.hits G a I v : ℝ) < (k + 2 : ℕ) := by
    have hb := hdecomp
    rw [hdecomp] at hnthreshold
    push_cast at hnthreshold
    have hbelow : (2 * a + 1 : ℝ) < (k + 2 : ℕ) := by
      rw [hdecomp]
      push_cast
      linarith
    rw [hdecomp] at hbelow
    exact lt_of_lt_of_le (lt_of_not_ge hnthreshold) (le_of_lt hbelow)
  have hnat : CurrentRounding.hits G a I v < k + 2 := by exact_mod_cast hlt
  omega

theorem other_gap_bound {v : V} (hv : v ∈ CurrentRounding.other G a I) :
    theta ≤ ((I).c v - (CurrentRounding.hits G a I v : ℝ)) := by
  have hh := other_hit_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap hv
  have hhR : (CurrentRounding.hits G a I v : ℝ) ≤ (k + 1 : ℕ) := by
    exact_mod_cast hh
  push_cast at hhR
  change theta ≤ (2 * a + 1) - (CurrentRounding.hits G a I v : ℝ)
  rw [hdecomp]
  push_cast
  nlinarith

theorem last_card_bound :
    ((CurrentRounding.last G a I).card : ℝ) ≤
      ((k + 1 : ℕ) : ℝ) * CurrentRounding.slack G a I / theta := by
  have hleft := CurrentRounding.leftover_bound G a I
  have hO : (∑ v ∈ CurrentRounding.other G a I,
      (CurrentRounding.hits G a I v : ℝ) * (I).x v) ≤
      (k + 1 : ℕ) * ∑ v ∈ CurrentRounding.other G a I, (I).x v := by
    calc
      _ ≤ ∑ v ∈ CurrentRounding.other G a I,
          ((k + 1 : ℕ) : ℝ) * (I).x v := by
        apply Finset.sum_le_sum
        intro v hv
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (other_hit_bound G a ha k theta hdecomp htheta0
            htheta1 hden x hx hcap hv)) ((I).nonneg v (CurrentRounding.other_subset G a I hv))
      _ = _ := by rw [← Finset.mul_sum]
  have hP : theta * ∑ v ∈ CurrentRounding.other G a I, (I).x v ≤
      CurrentRounding.slack G a I := by
    unfold CurrentRounding.slack
    calc
      _ = ∑ v ∈ CurrentRounding.other G a I, theta * (I).x v := by
        rw [Finset.mul_sum]
      _ ≤ ∑ v ∈ CurrentRounding.other G a I,
          ((I).c v - (CurrentRounding.hits G a I v : ℝ)) * (I).x v := by
        apply Finset.sum_le_sum
        intro v hv
        exact mul_le_mul_of_nonneg_right (other_gap_bound G a ha k theta hdecomp
          htheta0 htheta1 hden x hx hcap hv) ((I).nonneg v (CurrentRounding.other_subset G a I hv))
  have hratio : ((k + 1 : ℕ) : ℝ) *
      (∑ v ∈ CurrentRounding.other G a I, (I).x v) ≤
      ((k + 1 : ℕ) : ℝ) * CurrentRounding.slack G a I / theta := by
    apply (le_div_iff₀ htheta0).2
    calc
      ((k + 1 : ℕ) *
          (∑ v ∈ CurrentRounding.other G a I, (I).x v)) * theta =
          (k + 1 : ℕ) *
            (theta * ∑ v ∈ CurrentRounding.other G a I, (I).x v) := by ring
      _ ≤ (k + 1 : ℕ) * CurrentRounding.slack G a I :=
        mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _)
  exact hleft.trans (hO.trans hratio)

noncomputable def delta : ℝ := min
  ((1 - theta) / (a * (a + 1))) (theta / ((k + 1 : ℕ) : ℝ))

theorem delta_pos : 0 < delta a k theta := by
  unfold delta
  have hdenom : 0 < 1 - theta := sub_pos.mpr htheta1
  positivity

theorem count_bound :
    ((CurrentRounding.output G a I).card : ℝ) ≤
      (a / (1 - theta)) *
          ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card) +
        (((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I := by
  have hH := high_card_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap
  have hU := last_card_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap
  have hM : 1 ≤ a / (1 - theta) := by
    have hdenom : 0 < 1 - theta := by linarith
    rw [le_div_iff₀ hdenom]
    nlinarith
  have hsplit := CurrentRounding.output_card_split G a I
  have hreal : ((CurrentRounding.output G a I).card : ℝ) =
      (CurrentRounding.first G a I).card + (CurrentRounding.high G a I).card +
        (CurrentRounding.last G a I).card := by exact_mod_cast hsplit
  rw [hreal]
  have hw : (0 : ℝ) ≤ (CurrentRounding.first G a I).card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (CurrentRounding.middle G a I).card := Nat.cast_nonneg _
  have hp : 0 ≤ CurrentRounding.slack G a I :=
    CurrentRounding.slack_nonneg G a I (by
      intro v hv
      have hh := other_hit_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap hv
      have hhR : (CurrentRounding.hits G a I v : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast hh
      push_cast at hhR
      change (CurrentRounding.hits G a I v : ℝ) ≤ 2 * a + 1
      rw [hdecomp]
      push_cast
      linarith)
  have := hH
  have hH' : (CurrentRounding.high G a I).card ≤
      (a / (1 - theta)) * (CurrentRounding.middle G a I).card := by
    calc
      (CurrentRounding.high G a I).card ≤
          a * (CurrentRounding.middle G a I).card / (1 - theta) := hH
      _ = (a / (1 - theta)) * (CurrentRounding.middle G a I).card := by ring
  have hU' : (CurrentRounding.last G a I).card ≤
      (((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I := by
    calc
      (CurrentRounding.last G a I).card ≤
          ((k + 1 : ℕ) : ℝ) * CurrentRounding.slack G a I / theta := hU
      _ = (((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I := by ring
  nlinarith

/-- The exact noninteger branch count and its paying inequality. Here the
decomposition `2a=k+theta`, `0<theta<1` makes k the floor of `2a`. -/
theorem output_slack :
    ((CurrentRounding.high G a I).card : ℝ) ≤
        a * (CurrentRounding.middle G a I).card / (1 - theta) ∧
    ((CurrentRounding.last G a I).card : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * CurrentRounding.slack G a I / theta ∧
    delta a k theta * (CurrentRounding.output G a I).card ≤
      CurrentRounding.objective G a I - (CurrentRounding.output G a I).card := by
  have hcount := count_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap
  have hsave := CurrentRounding.selection_saving G a I ha hden (by
    intro v hv
    rfl)
  have hdelta := delta_pos G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap
  have hdeltaM : delta a k theta * (a / (1 - theta)) ≤ 1 / (a + 1) := by
    calc
      _ ≤ ((1 - theta) / (a * (a + 1))) * (a / (1 - theta)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _)
          (div_nonneg (by linarith) (sub_pos.mpr htheta1).le)
      _ = _ := by
        field_simp [ne_of_gt (sub_pos.mpr htheta1), ne_of_gt (mul_pos
          (by linarith : 0 < a) (by linarith : 0 < a + 1))]
  have hdeltaP : delta a k theta * (((k + 1 : ℕ) : ℝ) / theta) ≤ 1 := by
    calc
      _ ≤ (theta / ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / theta) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = _ := by
        field_simp [ne_of_gt htheta0, Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)]
  have hw : (0 : ℝ) ≤ (CurrentRounding.first G a I).card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (CurrentRounding.middle G a I).card := Nat.cast_nonneg _
  have hp : 0 ≤ CurrentRounding.slack G a I :=
    CurrentRounding.slack_nonneg G a I (by
      intro v hv
      have hh := other_hit_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap hv
      have hhR : (CurrentRounding.hits G a I v : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast hh
      push_cast at hhR
      change (CurrentRounding.hits G a I v : ℝ) ≤ 2 * a + 1
      rw [hdecomp]
      push_cast
      linarith)
  have hpay : delta a k theta * (CurrentRounding.output G a I).card ≤
      (CurrentRounding.first G a I).card / (a + 1) +
        (CurrentRounding.middle G a I).card / (a + 1) +
        CurrentRounding.slack G a I := by
    have hscaled := mul_le_mul_of_nonneg_left hcount hdelta.le
    have hfirst := mul_le_mul_of_nonneg_right hdeltaM (add_nonneg hw hl)
    have hlast := mul_le_mul_of_nonneg_right hdeltaP hp
    calc
      delta a k theta * (CurrentRounding.output G a I).card ≤
          delta a k theta *
            ((a / (1 - theta)) *
                ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card) +
              (((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I) := hscaled
      _ ≤ (CurrentRounding.first G a I).card / (a + 1) +
          (CurrentRounding.middle G a I).card / (a + 1) +
          CurrentRounding.slack G a I := by
        rw [mul_add]
        have hfirst' : delta a k theta *
            (a / (1 - theta) *
              ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card)) ≤
              ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card) /
                (a + 1) := by
          calc
            _ = (delta a k theta * (a / (1 - theta))) *
                ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card) := by ring
            _ ≤ (1 / (a + 1)) *
                ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card) := hfirst
            _ = _ := by ring
        have hlast' : delta a k theta *
            ((((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I) ≤
              CurrentRounding.slack G a I := by
          calc
            _ = (delta a k theta * (((k + 1 : ℕ) : ℝ) / theta)) *
                CurrentRounding.slack G a I := by ring
            _ ≤ 1 * CurrentRounding.slack G a I := hlast
            _ = _ := by ring
        have hsum : ((CurrentRounding.first G a I).card +
            (CurrentRounding.middle G a I).card : ℝ) / (a + 1) =
            (CurrentRounding.first G a I).card / (a + 1) +
              (CurrentRounding.middle G a I).card / (a + 1) := by ring
        calc
          _ = delta a k theta *
                (a / (1 - theta) *
                  ((CurrentRounding.first G a I).card + (CurrentRounding.middle G a I).card)) +
              delta a k theta *
                ((((k + 1 : ℕ) : ℝ) / theta) * CurrentRounding.slack G a I) := by ring
          _ ≤ ((CurrentRounding.first G a I).card +
                (CurrentRounding.middle G a I).card) / (a + 1) +
              CurrentRounding.slack G a I := add_le_add hfirst' hlast'
          _ = (CurrentRounding.first G a I).card / (a + 1) +
              (CurrentRounding.middle G a I).card / (a + 1) +
              CurrentRounding.slack G a I := by rw [hsum]
  refine ⟨high_card_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap,
    last_card_bound G a ha k theta hdecomp htheta0 htheta1 hden x hx hcap, ?_⟩
  have hsave' :
      (CurrentRounding.first G a I).card / (a + 1) +
        (CurrentRounding.middle G a I).card / (a + 1) +
        CurrentRounding.slack G a I ≤
      CurrentRounding.objective G a I - (CurrentRounding.output G a I).card := by
    convert hsave using 1 <;> ring
  exact hpay.trans hsave'

end Paper.CurrentNonintegerSlack
