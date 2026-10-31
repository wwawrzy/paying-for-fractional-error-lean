import Paper.Endpoints.Rounding.CurrentNonintegerSlack
import Paper.Endpoints.Rounding.CurrentBudgetBridge
import Paper.Endpoints.Rounding.NoncriticalOptimum

/-!
Mathematical transformation for the noninteger branch of `sc:thmB`.
This draft intentionally has no solver premise: the transformation is the
identity on the covering constraints, with comparison cost `b = 2a+1`.
It imports the separate slack draft directly from `tmp/proofs`. No compile
was run.
-/

namespace Paper.CurrentNonintegerTransformation

open SevenFoundation CurrentRounding
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/- The identity transformation keeps the ordinary domination constraints and
scales every unit objective coefficient by b. -/
noncomputable def transformedCost (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℝ) (x : V → ℝ) : ℝ :=
  ∑ v, b * x v

def transformedValues (b : ℝ) : Set ℝ :=
  {t | ∃ x, feasible (ordinary G) x ∧ transformedCost G b x = t}

noncomputable def transformedNumber (b : ℝ) : ℝ := sInf (transformedValues G b)

theorem transformedCost_eq (b : ℝ) (x : V → ℝ) :
    transformedCost G b x = b * cost (ordinary G) x := by
  rw [transformedCost, ordinary_cost]
  rw [Finset.mul_sum]

/-- The scaled LP has attained optimum exactly `(2a+1) * gf(G)`. This is a
statement about the transformed LP, not an assumption about an optimizer. -/
theorem transformed_optimum (b : ℝ) (hb : 0 ≤ b) :
    IsLeast (transformedValues G b) (b * fractionalNumber G) ∧
      transformedNumber G b = b * fractionalNumber G := by
  obtain ⟨y, hy, hyval, hymin⟩ := CurrentBudgetBridge.global_fractional_minimum G
  have hymin' : ∀ z, feasible (ordinary G) z →
      fractionalNumber G ≤ cost (ordinary G) z := by
    intro z hz
    rw [← hyval]
    exact hymin z hz
  have hleast : IsLeast (transformedValues G b) (b * fractionalNumber G) := by
    refine ⟨?_, ?_⟩
    · refine ⟨y, hy, ?_⟩
      rw [transformedCost_eq, hyval]
    · rintro t ⟨z, hz, rfl⟩
      rw [transformedCost_eq]
      exact mul_le_mul_of_nonneg_left (hymin' z hz) hb
  exact ⟨hleast, hleast.csInf_eq⟩

theorem endpoint_transformed_optimum (a : ℝ) (ha : 1 ≤ a) :
    IsLeast (transformedValues G (2 * a + 1)) ((2 * a + 1) * fractionalNumber G) ∧
      transformedNumber G (2 * a + 1) = (2 * a + 1) * fractionalNumber G := by
  exact transformed_optimum G (2 * a + 1) (by linarith)

/-- Every feasible unbounded LP vector can be capped coordinatewise. The cap
remains feasible, lies in `[0,1]^V`, and its constant-cost objective does not
exceed the original transformed cost. -/
theorem cap_for_rounding (a : ℝ) (ha : 1 ≤ a) (x : V → ℝ)
    (hx : feasible (ordinary G) x) :
    feasible (ordinary G) (PartialOptimum.cap x) ∧
      (∀ v, PartialOptimum.cap x v ≤ 1) ∧
      transformedCost G (2 * a + 1) (PartialOptimum.cap x) ≤
        transformedCost G (2 * a + 1) x := by
  have hLP : PartialOptimum.Feasible G Finset.univ x :=
    (NoncriticalOptimum.feasible_iff G x).mpr hx
  have hcapLP := PartialOptimum.cap_feasible G Finset.univ x hLP
  have hcapOrd := (NoncriticalOptimum.feasible_iff G (PartialOptimum.cap x)).mp hcapLP
  have hcapBound : ∀ v, PartialOptimum.cap x v ≤ 1 :=
    fun v => min_le_left 1 (x v)
  have hcostLP := PartialOptimum.cap_cost_le (fun _ : V => (1 : ℝ)) x
    (fun _ => zero_le_one)
  have hcostOrd : cost (ordinary G) (PartialOptimum.cap x) ≤
      cost (ordinary G) x := by
    simpa only [ordinary_cost, PartialOptimum.objective, one_mul] using hcostLP
  refine ⟨hcapOrd, hcapBound, ?_⟩
  rw [transformedCost_eq, transformedCost_eq]
  exact mul_le_mul_of_nonneg_left hcostOrd (by linarith)

noncomputable def rounded (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (theta : ℝ)
    (hdecomp : 2 * a = (k : ℝ) + theta)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : V → ℝ) (hx : feasible (ordinary G) x) : Finset V :=
  let hxLP := (NoncriticalOptimum.feasible_iff G x).mpr hx
  let hxcapLP := PartialOptimum.cap_feasible G Finset.univ x hxLP
  let hxcap := (NoncriticalOptimum.feasible_iff G (PartialOptimum.cap x)).mp hxcapLP
  let hcap : ∀ v, PartialOptimum.cap x v ≤ 1 := fun v => min_le_left 1 (x v)
  CurrentRounding.output G a
    (CurrentNonintegerSlack.uniformInput G a ha (PartialOptimum.cap x) hxcap hcap)

theorem universal_dominates (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (theta : ℝ)
    (hdecomp : 2 * a = (k : ℝ) + theta)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : V → ℝ) (hx : feasible (ordinary G) x) :
    dominates G (rounded G a ha k theta hdecomp htheta0 htheta1 x hx) := by
  let I := CurrentNonintegerSlack.uniformInput G a ha (PartialOptimum.cap x)
    ((NoncriticalOptimum.feasible_iff G (PartialOptimum.cap x)).mp
      (PartialOptimum.cap_feasible G Finset.univ x
        ((NoncriticalOptimum.feasible_iff G x).mpr hx)))
    (fun v => min_le_left 1 (x v))
  have hcover := CurrentRounding.output_covers G a I
  intro v
  apply hcover
  simp [I, CurrentNonintegerSlack.uniformInput]

/-- For every feasible original vector, the capped current rounding output
has the exact output-proportional slack measured against the original
transformed objective. -/
theorem universal_slack (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (theta : ℝ)
    (hdecomp : 2 * a = (k : ℝ) + theta)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hden : Incidence.InducedDensityBound G a)
    (x : V → ℝ) (hx : feasible (ordinary G) x) :
    CurrentNonintegerSlack.delta a k theta *
        (rounded G a ha k theta hdecomp htheta0 htheta1 x hx).card ≤
      transformedCost G (2 * a + 1) x -
        (rounded G a ha k theta hdecomp htheta0 htheta1 x hx).card := by
  obtain ⟨hxcap, hcap, hcostcap⟩ := cap_for_rounding G a ha x hx
  let I := CurrentNonintegerSlack.uniformInput G a ha (PartialOptimum.cap x) hxcap hcap
  have hslack := (CurrentNonintegerSlack.output_slack G a ha k theta hdecomp
    htheta0 htheta1 hden (PartialOptimum.cap x) hxcap hcap).2.2
  have hobj : CurrentRounding.objective G a I =
      transformedCost G (2 * a + 1) (PartialOptimum.cap x) := by
    simp [I, CurrentRounding.objective, CurrentNonintegerSlack.uniformInput,
      transformedCost, Finset.mul_sum]
  have hround : CurrentRounding.output G a I =
      rounded G a ha k theta hdecomp htheta0 htheta1 x hx := by
    rfl
  rw [hround, hobj] at hslack
  linarith

/- If a is rational and k is its floor, the exact real delta above is the
cast of the paper's fixed rational parameter. -/
def rationalTheta (a : ℚ) (k : ℕ) : ℚ := 2 * a - k

def rationalDelta (a : ℚ) (k : ℕ) : ℚ :=
  min ((1 - rationalTheta a k) / (a * (a + 1)))
    (rationalTheta a k / (k + 1))

theorem delta_cast (a : ℚ) (k : ℕ) :
    CurrentNonintegerSlack.delta (a : ℝ) k (rationalTheta a k : ℝ) =
      (rationalDelta a k : ℝ) := by
  simp [CurrentNonintegerSlack.delta, rationalDelta, rationalTheta]

/-- For noninteger `2a`, the chosen natural is exactly its floor, and the
real decomposition and rational accuracy used by `sc:thmB` agree. -/
theorem floor_parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    let k := ⌊2 * a⌋₊
    k = ⌊2 * a⌋₊ ∧ (k : ℚ) < 2 * a ∧ 2 * a < (k + 1 : ℕ) ∧
      0 < rationalTheta a k ∧ rationalTheta a k < 1 ∧
      2 * (a : ℝ) = (k : ℝ) + (rationalTheta a k : ℝ) ∧
      CurrentNonintegerSlack.delta (a : ℝ) k (rationalTheta a k : ℝ) =
        (rationalDelta a k : ℝ) := by
  dsimp only
  let k : ℕ := ⌊2 * a⌋₊
  have hk_le : (k : ℚ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hk_lt : 2 * a < (k + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one (2 * a)
  have hk_ne : (k : ℚ) ≠ 2 * a := by
    intro heq
    apply hnoninteger
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast heq
  have hk_lower : (k : ℚ) < 2 * a := lt_of_le_of_ne hk_le hk_ne
  have htheta0 : 0 < rationalTheta a k := by
    dsimp [rationalTheta]
    linarith
  have htheta1 : rationalTheta a k < 1 := by
    dsimp [rationalTheta]
    push_cast at hk_lt ⊢
    linarith
  have hdecomp : 2 * (a : ℝ) = (k : ℝ) + (rationalTheta a k : ℝ) := by
    dsimp [rationalTheta]
    push_cast
    ring
  exact ⟨rfl, hk_lower, hk_lt, htheta0, htheta1, hdecomp, delta_cast a k⟩

end Paper.CurrentNonintegerTransformation
