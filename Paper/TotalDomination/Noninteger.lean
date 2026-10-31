import Paper.TotalDomination.CostSaving
import Paper.Certificates.Counting.CoveringOptimum

/-! The mathematical rounding bound of `fv:total:noncrit`. The decomposition
`2a = k + theta`, with `0 < theta < 1`, identifies the integer floor. All
mass estimates concern the actual selection sets. Capping handles arbitrary
nonnegative feasible inputs. This file does not implement the four broadcasts. -/

namespace Paper.TotalDomination.Noninteger

open scoped BigOperators

structure Parameters where
  a : ℝ
  a_ge_one : 1 ≤ a
  k : ℕ
  theta : ℝ
  decomposition : 2 * a = k + theta
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  mu : ℝ
  mu_pos : 0 < mu
  mu_le_theta : mu ≤ theta
  admissible : (1 + mu) * (1 + mu - theta) ≤ 2 * (1 - theta)

noncomputable def threshold (p : Parameters) : ℝ := (1 + p.mu) / (2 * p.a)

theorem threshold_pos (p : Parameters) : 0 < threshold p := by
  apply div_pos <;> linarith [p.mu_pos, p.a_ge_one]

theorem cutoff_bound (p : Parameters) : 2 * p.a ≤ (p.k + 1 : ℕ) := by
  push_cast
  linarith [p.decomposition, p.theta_lt_one]

theorem threshold_identity (p : Parameters) : threshold p * p.a = (1 + p.mu) / 2 := by
  have ha : p.a ≠ 0 := by linarith [p.a_ge_one]
  unfold threshold
  field_simp

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def input (p : Parameters) (ids : V → ℕ)
    (hfree : ∀ r, (G.neighborFinset r).Nonempty) (x : V → ℝ) : Input G where
  candidates := Finset.univ
  demands := Finset.univ
  eligible := Finset.univ
  eligible_subset := Finset.Subset.rfl
  x := x
  threshold := threshold p
  cutoff := p.k + 1
  identifier := ids
  isolate_free := hfree

variable (p : Parameters) (ids : V → ℕ)
variable (hfree : ∀ r, (G.neighborFinset r).Nonempty) (x : V → ℝ)

local notation "I" => input G p ids hfree x
local notation "W" => TotalDomination.first G I
local notation "H" => TotalDomination.high G I
local notation "O" => TotalDomination.other G I
local notation "j" => TotalDomination.surplus G I
local notation "P" => TotalDomination.penalty G I (fun _ => 2 * p.a)

theorem high_weight {v : V} (hv : v ∈ H) : x v ≤ threshold p := by
  classical
  have hnW := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  by_contra hn
  exact hnW (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hn⟩)

theorem other_hit_bound {v : V} (hv : v ∈ O) : TotalDomination.hits G I v ≤ p.k := by
  classical
  have hnWH := (Finset.mem_sdiff.mp hv).2
  have hnW : v ∉ W := fun hw => hnWH (Finset.mem_union_left _ hw)
  have hnH : v ∉ H := fun hh => hnWH (Finset.mem_union_right _ hh)
  by_contra hn
  exact hnH (Finset.mem_filter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnW⟩, by
      change p.k + 1 ≤ TotalDomination.hits G I v
      omega⟩)

theorem other_gap_bound {v : V} (hv : v ∈ O) :
    p.theta ≤ 2 * p.a - (TotalDomination.hits G I v : ℝ) := by
  have hh : (TotalDomination.hits G I v : ℝ) ≤ p.k := by
    exact_mod_cast other_hit_bound G p ids hfree x hv
  linarith [p.decomposition]

theorem high_card_bound (hden : Incidence.InducedDensityBound G p.a) :
    ((H).card : ℝ) ≤ p.a * j / (1 - p.theta) := by
  classical
  have hpoint : ∀ v ∈ H,
      1 - p.theta ≤ (TotalDomination.hits G I v : ℝ) - 2 * p.a := by
    intro v hv
    have hn : (p.k + 1 : ℕ) ≤ (TotalDomination.hits G I v : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hv).2
    push_cast at hn
    linarith [p.decomposition]
  have hE : (1 - p.theta) * ((H).card : ℝ) ≤ TotalDomination.excess G I p.a := by
    calc
      _ = ∑ _v ∈ H, (1 - p.theta) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun v hv => hpoint v hv
  have hd := TotalDomination.excess_le G I p.a hden
  apply (le_div_iff₀ (by linarith [p.theta_lt_one] : 0 < 1 - p.theta)).2
  nlinarith only [hE, hd]

theorem other_mass_bound (hx : ∀ v, 0 ≤ x v) : (∑ v ∈ O, x v) ≤ P / p.theta := by
  have hs : p.theta * (∑ v ∈ O, x v) ≤ P := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_right (other_gap_bound G p ids hfree x hv) (hx v)
  apply (le_div_iff₀ p.theta_pos).2
  nlinarith only [hs]

theorem mass_partition :
    (∑ v, x v) = (∑ v ∈ W, x v) + (∑ v ∈ H, x v) + (∑ v ∈ O, x v) := by
  classical
  have hs := Finset.sum_sdiff (s₁ := W ∪ H) (s₂ := (Finset.univ : Finset V))
    (f := x) (Finset.subset_univ _)
  rw [Finset.sum_union (TotalDomination.high_disjoint_first G I).symm] at hs
  change (∑ v ∈ O, x v) + ((∑ v ∈ W, x v) + (∑ v ∈ H, x v)) = ∑ v, x v at hs
  linarith

theorem mass_bound (hden : Incidence.InducedDensityBound G p.a)
    (hx : ∀ v, 0 ≤ x v) (hcap : ∀ v, x v ≤ 1) :
    (∑ v, x v) ≤ (W).card + (threshold p * p.a / (1 - p.theta)) * j + P / p.theta := by
  have hw : (∑ v ∈ W, x v) ≤ ((W).card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ W, (1 : ℝ) := Finset.sum_le_sum fun v _ => hcap v
      _ = _ := by simp
  have hh : (∑ v ∈ H, x v) ≤ threshold p * ((H).card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ H, threshold p :=
        Finset.sum_le_sum fun v hv => high_weight G p ids hfree x hv
      _ = _ := by simp [mul_comm]
  have hcard := mul_le_mul_of_nonneg_left (high_card_bound G p ids hfree x hden)
    (threshold_pos p).le
  rw [show threshold p * (p.a * j / (1 - p.theta)) =
    (threshold p * p.a / (1 - p.theta)) * j by ring] at hcard
  have ho := other_mass_bound G p ids hfree x hx
  rw [mass_partition G p ids hfree x]
  linarith only [hw, hh, hcard, ho]

/-- Exact coefficient comparison, using the paper's quadratic μ condition. -/
theorem surplus_coefficient :
    p.mu * (threshold p * p.a / (1 - p.theta)) ≤ 1 - p.a * threshold p := by
  rw [threshold_identity, mul_comm p.a (threshold p), threshold_identity]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by linarith [p.theta_lt_one] : 0 < 1 - p.theta)).2
  nlinarith only [p.admissible]

/-- The actual selected set totally dominates and saves μ times the input mass.
The assumptions concern only the input vector and scalar parameters. -/
theorem rounding_bound (hden : Incidence.InducedDensityBound G p.a)
    (hx : ∀ v, 0 ≤ x v) (hcap : ∀ v, x v ≤ 1)
    (hcover : ∀ r, 1 ≤ ∑ v ∈ G.neighborFinset r, x v) :
    (∀ r, ∃ v ∈ TotalDomination.output G I, G.Adj r v) ∧
      ((TotalDomination.output G I).card : ℝ) ≤ (2 * p.a - p.mu) * ∑ v, x v := by
  classical
  refine ⟨TotalDomination.output_total_dominates G I rfl, ?_⟩
  have hR2 : ∀ v ∈ O, (TotalDomination.hits G I v : ℝ) ≤ 2 * p.a := by
    intro v hv
    have hh := other_gap_bound G p ids hfree x hv
    linarith [p.theta_pos]
  have hs := TotalDomination.rounding_saving G I p.a (by linarith [p.a_ge_one]) hden
    (cutoff_bound p) (threshold_pos p) (fun _ => 2 * p.a) (fun v _ => hx v)
    (by intro v hv; exact False.elim (hv (Finset.mem_univ _)))
    (fun r _ => hcover r) (fun _ _ => rfl) hR2
    (fun v hv _ => high_weight G p ids hfree x hv)
  have hj := TotalDomination.surplus_nonneg G I p.a (by linarith [p.a_ge_one]) hden
    (cutoff_bound p)
  have hmass := mul_le_mul_of_nonneg_left (mass_bound G p ids hfree x hden hx hcap) p.mu_pos.le
  have hmass' : p.mu * (∑ v, x v) ≤ p.mu * ((W).card : ℝ) +
      (p.mu * (threshold p * p.a / (1 - p.theta))) * j + (p.mu / p.theta) * P := by
    calc
      _ ≤ _ := hmass
      _ = _ := by ring
  have hcoef := mul_le_mul_of_nonneg_right (surplus_coefficient p) hj
  have hpcoef : p.mu / p.theta ≤ 1 := by
    apply (div_le_iff₀ p.theta_pos).2
    simpa using p.mu_le_theta
  have hp := mul_le_mul_of_nonneg_right hpcoef hs.1
  have hobjective : TotalDomination.objective G I (fun _ => 2 * p.a) =
      2 * p.a * ∑ v, x v := by simp [TotalDomination.objective, input, Finset.mul_sum]
  have ht := threshold_identity p
  change (threshold p) * p.a = (1 + p.mu) / 2 at ht
  rw [hobjective] at hs
  change 0 ≤ P ∧ 0 ≤ TotalDomination.oversupply G I ∧
    (2 * p.a * threshold p - 1) * ((W).card : ℝ) +
      (1 - p.a * threshold p) * j + P + TotalDomination.oversupply G I ≤
      2 * p.a * (∑ v, x v) - (TotalDomination.output G I).card at hs
  have hfirstcoef : 2 * p.a * threshold p - 1 = p.mu := by nlinarith only [ht]
  rw [hfirstcoef] at hs
  nlinarith only [hmass', hcoef, hp, hs.2.1, hs.2.2]

/-- Capping preserves total fractional feasibility and cannot increase mass.
This covers the paper's arbitrary nonnegative feasible input, rather
than assuming that every input coordinate was already at most one. -/
theorem capped_rounding_bound (hden : Incidence.InducedDensityBound G p.a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ x) :
    let Ic := input G p ids hfree (CoveringOptimum.cap x)
    (∀ r, ∃ v ∈ TotalDomination.output G Ic, G.Adj r v) ∧
      ((TotalDomination.output G Ic).card : ℝ) ≤ (2 * p.a - p.mu) * ∑ v, x v := by
  have hcap := CoveringOptimum.cap_feasible (fun r => G.neighborFinset r) Finset.univ x hx
  obtain ⟨hdom, hbound⟩ := rounding_bound G p ids hfree (CoveringOptimum.cap x) hden hcap.1
    (fun v => min_le_left 1 (x v)) (fun r => hcap.2 r (Finset.mem_univ _))
  refine ⟨hdom, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun v _ => min_le_right 1 (x v)
  · linarith [p.a_ge_one, p.mu_le_theta, p.theta_lt_one]

end Paper.TotalDomination.Noninteger

#print axioms Paper.TotalDomination.Noninteger.high_card_bound
#print axioms Paper.TotalDomination.Noninteger.other_mass_bound
#print axioms Paper.TotalDomination.Noninteger.mass_bound
#print axioms Paper.TotalDomination.Noninteger.rounding_bound
#print axioms Paper.TotalDomination.Noninteger.capped_rounding_bound
