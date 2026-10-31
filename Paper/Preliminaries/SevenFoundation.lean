import Mathlib

/-!
# the covering paper: exact-seven foundation, not a complete planar algorithm certificate

Source: paper_7apx/stoc_paper.pdf, C.17-C.18, D.1, E.3, E.16.
This file proves elementary interfaces, domination of the actual set construction,
and the final scalar error cancellation. It does NOT construct the distributed
fractional solver or prove the planar saving and defect estimates.
The final theorem is explicitly conditional on those unproved estimates.
-/

namespace Paper.SevenFoundation

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Closed-neighborhood incidence, including self-domination. -/
def closed (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (fun u => u = v ∨ G.Adj v u)

theorem mem_closed (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    u ∈ closed G v ↔ u = v ∨ G.Adj v u := by
  simp [closed]

theorem self_mem_closed (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ closed G v := by simp [closed]

theorem closed_symm (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    u ∈ closed G v ↔ v ∈ closed G u := by
  simp only [mem_closed]
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr h.symm
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- Partial covering instance, with explicit admissible candidates per demand.
Coordinates outside the candidate set are required to vanish. -/
structure CoverInstance (V : Type*) [Fintype V] [DecidableEq V] where
  demands : Finset V
  candidates : Finset V
  eligible : V → Finset V
  eligible_subset : ∀ r ∈ demands, eligible r ⊆ candidates
  cost : V → ℝ
  cost_nonneg : ∀ v, 0 ≤ cost v

def feasible (I : CoverInstance V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ (∀ v ∉ I.candidates, x v = 0) ∧
    ∀ r ∈ I.demands, 1 ≤ ∑ v ∈ I.eligible r, x v

noncomputable def cost (I : CoverInstance V) (x : V → ℝ) : ℝ :=
  ∑ v, I.cost v * x v

/-- Comparison against every feasible competitor avoids assuming LP attainment. -/
def approximates (I : CoverInstance V) (factor : ℝ) (x : V → ℝ) : Prop :=
  feasible I x ∧ ∀ y, feasible I y → cost I x ≤ factor * cost I y

def ordinary (G : SimpleGraph V) [DecidableRel G.Adj] : CoverInstance V where
  demands := Finset.univ
  candidates := Finset.univ
  eligible := closed G
  eligible_subset := by intros; exact Finset.subset_univ _
  cost := fun _ => 1
  cost_nonneg := by intro; norm_num

theorem ordinary_cost (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    cost (ordinary G) x = ∑ v, x v := by simp [cost, ordinary]

theorem feasible_convex_combination (I : CoverInstance V) (x y : V → ℝ)
    (hx : feasible I x) (hy : feasible I y) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    feasible I (fun v => p * x v + (1 - p) * y v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact add_nonneg (mul_nonneg hp (hx.1 v)) (mul_nonneg (sub_nonneg.mpr hp1) (hy.1 v))
  · intro v hv
    simp [hx.2.1 v hv, hy.2.1 v hv]
  · intro r hr
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2.2 r hr) hp
    have h2 := mul_le_mul_of_nonneg_left (hy.2.2 r hr) (sub_nonneg.mpr hp1)
    nlinarith

theorem cost_convex_combination (I : CoverInstance V) (x y : V → ℝ) (p : ℝ) :
    cost I (fun v => p * x v + (1 - p) * y v) =
      p * cost I x + (1 - p) * cost I y := by
  simp only [cost, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Neighborhood union. Its use here is a mathematical set specification,
not a claim that the network gathers an unbounded neighborhood. -/
def covered (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S.biUnion (closed G)

def dominates (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ v, v ∈ covered G S

theorem covered_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (h : S ⊆ T) : covered G S ⊆ covered G T := by
  intro v hv
  obtain ⟨u, hu, huv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨u, h hu, huv⟩

theorem subset_covered (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    S ⊆ covered G S := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨v, hv, self_mem_closed G v⟩

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

theorem indicator_feasible (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : dominates G S) : feasible (ordinary G) (indicator S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp only [indicator]
    split_ifs <;> norm_num
  · intro v hv
    exact False.elim (hv (Finset.mem_univ v))
  · intro r _
    obtain ⟨v, hvS, hrv⟩ := Finset.mem_biUnion.mp (hS r)
    have hvr : v ∈ closed G r := (closed_symm G r v).mp hrv
    have h := Finset.single_le_sum (fun i (_ : i ∈ closed G r) =>
      show (0 : ℝ) ≤ indicator S i by unfold indicator; split_ifs <;> norm_num) hvr
    simpa [ordinary, indicator, hvS] using h

theorem indicator_cost (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cost (ordinary G) (indicator S) = (S.card : ℝ) := by
  simp [ordinary_cost, indicator]

theorem cost_nonneg_of_feasible (I : CoverInstance V) (x : V → ℝ)
    (hx : feasible I x) : 0 ≤ cost I x := by
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (I.cost_nonneg v) (hx.1 v))

def feasibleCosts (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℝ :=
  {t | ∃ x, feasible (ordinary G) x ∧ cost (ordinary G) x = t}

noncomputable def fractionalNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf (feasibleCosts G)

theorem feasibleCosts_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] :
    (feasibleCosts G).Nonempty := by
  have hd : dominates G (Finset.univ : Finset V) := by
    intro v
    exact subset_covered G _ (Finset.mem_univ v)
  exact ⟨_, indicator Finset.univ, indicator_feasible G _ hd, rfl⟩

theorem feasibleCosts_bddBelow (G : SimpleGraph V) [DecidableRel G.Adj] :
    BddBelow (feasibleCosts G) := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact cost_nonneg_of_feasible _ _ hx

theorem fractionalNumber_le_integral (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : dominates G S) : fractionalNumber G ≤ (S.card : ℝ) := by
  apply csInf_le (feasibleCosts_bddBelow G)
  exact ⟨indicator S, indicator_feasible G S hS, indicator_cost G S⟩

/-- This bridge does not require an optimum vector to be chosen. -/
theorem universal_bound_to_fractionalNumber (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V)
    (h : ∀ y, feasible (ordinary G) y → (D.card : ℝ) ≤ 7 * cost (ordinary G) y) :
    (D.card : ℝ) ≤ 7 * fractionalNumber G := by
  have hlow : (D.card : ℝ) / 7 ≤ fractionalNumber G := by
    apply le_csInf (feasibleCosts_nonempty G)
    rintro t ⟨y, hy, rfl⟩
    have hb := h y hy
    linarith
  linarith

/-- A bound against every fractional cover also bounds every integral cover. -/
theorem fractional_bound_implies_integral_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (D S : Finset V) (factor : ℝ) (hS : dominates G S)
    (h : ∀ y, feasible (ordinary G) y → (D.card : ℝ) ≤ factor * cost (ordinary G) y) :
    (D.card : ℝ) ≤ factor * (S.card : ℝ) := by
  simpa only [indicator_cost] using h (indicator S) (indicator_feasible G S hS)

def defects (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v ≠ 6)

def zone (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  covered G (covered G (defects G))

def far (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ \ zone G

def initialDemands (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  zone G \ covered G (far G)

noncomputable def boundaryCost (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  7 - ((closed G v ∩ far G).card : ℝ)

noncomputable def first (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V := by
  classical
  exact (zone G).filter (fun v => 7 ≤ G.degree v ∧ (1 : ℝ) / 4 < x v)

noncomputable def residual (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  initialDemands G \ covered G (first G x)

noncomputable def high (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (zone G \ first G x).filter (fun v => 7 ≤ (closed G v ∩ residual G x).card)

noncomputable def last (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  residual G x \ covered G (high G x)

noncomputable def localOutput (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  first G x ∪ high G x ∪ last G x

noncomputable def output (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  far G ∪ localOutput G x

/-- Domination is unconditional in x. Accuracy and planarity are needed for size. -/
theorem output_dominates (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    dominates G (output G x) := by
  classical
  intro v
  have hF : far G ⊆ output G x := Finset.subset_union_left
  have hW : first G x ⊆ output G x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hH : high G x ⊆ output G x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
  have hU : last G x ⊆ output G x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hu)
  by_cases hvF : v ∈ covered G (far G)
  · exact covered_mono G hF hvF
  have hvZ : v ∈ zone G := by
    by_contra hn
    have hf : v ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
    exact hvF (subset_covered G _ hf)
  have hr0 : v ∈ initialDemands G := Finset.mem_sdiff.mpr ⟨hvZ, hvF⟩
  by_cases hvW : v ∈ covered G (first G x)
  · exact covered_mono G hW hvW
  have hr : v ∈ residual G x := Finset.mem_sdiff.mpr ⟨hr0, hvW⟩
  by_cases hvH : v ∈ covered G (high G x)
  · exact covered_mono G hH hvH
  exact subset_covered G _ (hU (Finset.mem_sdiff.mpr ⟨hr, hvH⟩))

/-- Arithmetic only: the two graph inequalities are still separate obligations. -/
theorem planar_error_paid {tau w ell slack : ℝ}
    (hw : 0 ≤ w) (hl : 0 ≤ ell) (hp : 0 ≤ slack)
    (hcontrol : tau ≤ 784 * w + 1036 * ell + 1554 * slack) :
    tau / 10000 ≤ (3 / 4 : ℝ) * w + (1 / 4 : ℝ) * ell + slack := by
  linarith

theorem error_cancellation {tau computed selected saving delta : ℝ}
    (haccuracy : computed ≤ (1 + delta) * tau)
    (hsaving : saving ≤ computed - selected)
    (hpaid : delta * tau ≤ saving) : selected ≤ tau := by
  nlinarith

/-- Conditional endpoint: this theorem does not establish its planar hypotheses. -/
theorem conditional_exact_seven (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℝ) (tau computed w ell slack : ℝ)
    (hw : 0 ≤ w) (hl : 0 ≤ ell) (hp : 0 ≤ slack)
    (hbudget : ((far G).card : ℝ) + tau ≤ 7 * cost (ordinary G) y)
    (haccuracy : computed ≤ (1 + (1 : ℝ) / 10000) * tau)
    (hsaving : (3 / 4 : ℝ) * w + (1 / 4 : ℝ) * ell + slack ≤
      computed - ((localOutput G x).card : ℝ))
    (hcontrol : tau ≤ 784 * w + 1036 * ell + 1554 * slack) :
    dominates G (output G x) ∧ ((output G x).card : ℝ) ≤ 7 * cost (ordinary G) y := by
  refine ⟨output_dominates G x, ?_⟩
  have hpaid := planar_error_paid hw hl hp hcontrol
  have hlocal : ((localOutput G x).card : ℝ) ≤ tau := by linarith
  have hcard := Finset.card_union_le (far G) (localOutput G x)
  have hc : ((output G x).card : ℝ) ≤ ((far G).card : ℝ) + ((localOutput G x).card : ℝ) := by
    exact_mod_cast hcard
  linarith

end Paper.SevenFoundation
