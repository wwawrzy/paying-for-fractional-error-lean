import Paper.Endpoints.Bounds.CurrentCriticalKT0
import Paper.Communication.CurrentNonintegerProgram
import Paper.Endpoints.Rounding.CurrentNonintegerTransformation
import Paper.Endpoints.Rounding.Slack

/-!
Paper-facing Theorem B, with two explicit rational-density branches.
The integer branch uses exactly F=V\N[B] and its current residual LP.
The noninteger branch assumes only subgraph (induced-set) density, uses
the identity transformation and the exact current rational slack, and
implements the same capped rounding by three one-bit broadcasts.

There is no solver premise in either slack certificate. The final payment
implication takes only the relative cost hypothesis stated in Theorem B.
All natural threshold parameters are fixed before the graph and input.
-/

namespace Paper.CurrentTheoremB

open BroadcastModel SevenFoundation

/-- The first assertion of Theorem B, independent of graphs or LP
representations. This is a direct specialization of the abstract principle. -/
theorem pays_for_fractional_error {δ cost output optimum : ℝ} (hδ : 0 < δ)
    (hslack : (1 + δ) * output ≤ cost)
    (hcost : cost ≤ (1 + δ) * optimum) : output ≤ optimum :=
  Slack.pays_for_error hδ hslack hcost

/-- The rational integer hypothesis in the paper yields a natural degree
parameter; no integer-to-natural conversion is left as an endpoint premise. -/
theorem integer_degree (a : ℚ) (ha : 1 ≤ a)
    (hinteger : ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ d : ℕ, (d : ℝ) = 2 * (a : ℝ) := by
  obtain ⟨z, hz⟩ := hinteger
  have hzQ : (0 : ℚ) ≤ (z : ℚ) := by rw [hz]; linarith
  have hz0 : 0 ≤ z := by exact_mod_cast hzQ
  have hdz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hdQ : (z.toNat : ℚ) = 2 * a := by
    calc
      _ = (z : ℚ) := by exact_mod_cast hdz
      _ = _ := hz
  exact ⟨z.toNat, by exact_mod_cast hdQ⟩

/-- Integer branch of the second assertion of Theorem B. The transformed
optimum budget and slack hold for every feasible vector of the unbounded
nonnegative auxiliary LP; the rounding includes a local cap. The actual
instance transformation takes two one-bit KT1 rounds, or three KT0 rounds
including the initial exchange of identifiers. -/
theorem integer_branch (a : ℚ) (ha : 1 ≤ a)
    (hinteger : ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ d : ℕ, ∃ hd : (d : ℝ) = 2 * (a : ℝ),
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) →
        let δ := 1 / (2 * (a : ℝ) * (2 * (a : ℝ) + 1) ^ 2)
        0 < δ ∧
          CurrentBudget.auxiliaryNumber G d ≤
            (2 * (a : ℝ) + 1) * fractionalNumber G - (CurrentBudget.selected G d).card ∧
          (CurrentZoneProgram.program (V := V) d).rounds = 2 ∧
          (CurrentZoneProgram.program (V := V) d).maxBits = 1 ∧
          (∀ (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G d) x),
            let D := CurrentRounding.output G (a : ℝ)
              (CurrentCriticalKT0.cappedInput G (a : ℝ) d hd x hx)
            (1 + δ) * D.card ≤ cost (CurrentBudget.auxiliary G d) x ∧
              (cost (CurrentBudget.auxiliary G d) x ≤
                (1 + δ) * CurrentBudget.auxiliaryNumber G d →
                (D.card : ℝ) ≤ CurrentBudget.auxiliaryNumber G d)) ∧
          ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
            (CurrentCriticalKT0.preprocess C d).rounds = 3 ∧
              (CurrentCriticalKT0.preprocess C d).maxBits = max b 1 ∧
              (CurrentCriticalKT0.preprocess C d).runEncoded G ports (fun _ => ()) =
                CurrentZoneProgram.expected G d := by
  obtain ⟨d, hd⟩ := integer_degree a ha hinteger
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  refine ⟨d, hd, ?_⟩
  intro V _ _ G _ hden
  obtain ⟨hδ, hbudget, hrounds, hbits, hslack⟩ :=
    CurrentCriticalKT0.integer_transformation_all_feasible G (a : ℝ) haR d hd hden
  refine ⟨hδ, hbudget, hrounds, hbits, ?_, ?_⟩
  · intro x hx
    dsimp only
    have hs := hslack x hx
    exact ⟨hs, fun hc => Slack.pays_for_error hδ hs hc⟩
  · intro ports b C
    exact ⟨CurrentCriticalKT0.preprocess_rounds C d,
      CurrentCriticalKT0.preprocess_maxBits C d,
      CurrentCriticalKT0.preprocess_correct G ports C d⟩

def degreeFloor (a : ℚ) : ℕ := ⌊2 * a⌋₊

def theta (a : ℚ) : ℚ := CurrentNonintegerTransformation.rationalTheta a (degreeFloor a)

def delta (a : ℚ) : ℚ := CurrentNonintegerTransformation.rationalDelta a (degreeFloor a)

theorem noninteger_decomposition (a : ℚ) :
    2 * (a : ℝ) = (degreeFloor a : ℝ) + (theta a : ℝ) := by
  unfold theta CurrentNonintegerTransformation.rationalTheta
  push_cast
  ring

theorem theta_pos (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) : 0 < (theta a : ℝ) := by
  obtain ⟨_, _, _, ht, _, _, _⟩ :=
    CurrentNonintegerTransformation.floor_parameters a ha hnoninteger
  exact_mod_cast ht

theorem theta_lt_one (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) : (theta a : ℝ) < 1 := by
  obtain ⟨_, _, _, _, ht, _, _⟩ :=
    CurrentNonintegerTransformation.floor_parameters a ha hnoninteger
  exact_mod_cast ht

theorem delta_eq (a : ℚ) :
    CurrentNonintegerSlack.delta (a : ℝ) (degreeFloor a) (theta a : ℝ) = (delta a : ℝ) :=
  CurrentNonintegerTransformation.delta_cast a (degreeFloor a)

section NonintegerRounding

variable {V : Type} [DecidableEq V]

/-- Capping is local, so the exact current noninteger rounding still
requires three broadcasts on every feasible nonnegative input. -/
def nonintegerProgram (k m h D N : ℕ) : Program V (Fin N) Bool :=
  .seq (.local fun _ _ p => CappedWholeProgram.cap D p)
    (CurrentNonintegerProgram.program k m h D (D + 1))

theorem noninteger_rounds (k m h D N : ℕ) :
    (nonintegerProgram (V := V) k m h D N).rounds = 3 := rfl

theorem noninteger_maxBits (k m h D N : ℕ) :
    (nonintegerProgram (V := V) k m h D N).maxBits = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def nonintegerRounded (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (x : V → ℝ) (hx : feasible (ordinary G) x) : Finset V :=
  CurrentNonintegerTransformation.rounded G (a : ℝ) (by exact_mod_cast ha)
    (degreeFloor a) (theta a : ℝ) (noninteger_decomposition a)
    (theta_pos a ha hnoninteger) (theta_lt_one a ha hnoninteger) x hx

theorem input_eq_uniform (a : ℝ) (ha : 1 ≤ a) (x y : V → ℝ) (he : x = y)
    (hx : PartialOptimum.Feasible G Finset.univ x) (hy : feasible (ordinary G) y)
    (hc : ∀ v, x v ≤ 1) (hd : ∀ v, y v ≤ 1) :
    CurrentNonintegerProgram.input G a ha x hx hc =
      CurrentNonintegerSlack.uniformInput G a ha y hy hd := by
  subst y
  rfl

/-- The three-round program computes exactly the same capped set as the
universal, solver-independent mathematical slack certificate. -/
theorem noninteger_encoded_correct (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (hratio : (h : ℝ) / m = 1 / ((a : ℝ) + 1)) (p : V → Fin N)
    (hx : feasible (ordinary G) (fun v => ((p v).val : ℝ) / D)) :
    (nonintegerProgram (degreeFloor a) m h D N).runEncoded G p =
      fun v => decide (v ∈ nonintegerRounded G a ha hnoninteger
        (fun u => ((p u).val : ℝ) / D) hx) := by
  let x := fun v => ((p v).val : ℝ) / D
  let q := fun v => CappedWholeProgram.cap D (p v)
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hxLP := (NoncriticalOptimum.feasible_iff G x).mpr hx
  have hcapLP := PartialOptimum.cap_feasible G Finset.univ x hxLP
  have hcapOrd := (NoncriticalOptimum.feasible_iff G (PartialOptimum.cap x)).mp hcapLP
  have he : (fun v => ((q v).val : ℝ) / D) = PartialOptimum.cap x := by
    funext v
    exact CappedWholeProgram.cap_value D hD (p v)
  have hy : PartialOptimum.Feasible G Finset.univ (fun v => ((q v).val : ℝ) / D) := by
    rw [he]
    exact hcapLP
  have hcap : ∀ v, ((q v).val : ℝ) / D ≤ 1 := by
    intro v
    rw [congrFun he v]
    exact min_le_left _ _
  have hk : (degreeFloor a : ℝ) < 2 * (a : ℝ) := by
    have ht := theta_pos a ha hnoninteger
    have hd := noninteger_decomposition a
    linarith
  have hk1 : 2 * (a : ℝ) < ((degreeFloor a + 1 : ℕ) : ℝ) := by
    have ht := theta_lt_one a ha hnoninteger
    have hd := noninteger_decomposition a
    push_cast
    linarith
  have hs := CurrentNonintegerProgram.encoded_correct G (degreeFloor a) m h D (D + 1)
    hm hD (a : ℝ) haR hk hk1 hratio q hy hcap
  have hi := input_eq_uniform G (a : ℝ) haR _ _ he hy hcapOrd hcap
    (fun v => min_le_left 1 (x v))
  rw [hi] at hs
  change (CurrentNonintegerProgram.program (degreeFloor a) m h D (D + 1)).runEncoded G q = _
  simpa only [nonintegerRounded, CurrentNonintegerTransformation.rounded] using hs

end NonintegerRounding

/-- Noninteger branch of Theorem B. Parameters m,h are chosen before G.
The mathematical conclusion needs only induced-set/subgraph density a;
no minor-density or solver assumption is introduced. The broadcast
implementation works for every positive input denominator and finite
numerator range, also chosen before G. -/
theorem noninteger_branch (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ m h : ℕ, 0 < m ∧ (h : ℝ) / m = 1 / ((a : ℝ) + 1) ∧
      (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Incidence.InducedDensityBound G (a : ℝ) →
        0 < (delta a : ℝ) ∧
          IsLeast (CurrentNonintegerTransformation.transformedValues G (2 * (a : ℝ) + 1))
            ((2 * (a : ℝ) + 1) * fractionalNumber G) ∧
          CurrentNonintegerTransformation.transformedNumber G (2 * (a : ℝ) + 1) =
            (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          ∀ (x : V → ℝ) (hx : feasible (ordinary G) x),
            let D := nonintegerRounded G a ha hnoninteger x hx
            dominates G D ∧
              (1 + (delta a : ℝ)) * D.card ≤
                CurrentNonintegerTransformation.transformedCost G (2 * (a : ℝ) + 1) x ∧
              (CurrentNonintegerTransformation.transformedCost G (2 * (a : ℝ) + 1) x ≤
                (1 + (delta a : ℝ)) *
                  CurrentNonintegerTransformation.transformedNumber G (2 * (a : ℝ) + 1) →
                (D.card : ℝ) ≤
                  CurrentNonintegerTransformation.transformedNumber G (2 * (a : ℝ) + 1))) ∧
      ∀ D N : ℕ, 0 < D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          (nonintegerProgram (V := V) (degreeFloor a) m h D N).rounds = 3 ∧
            (nonintegerProgram (V := V) (degreeFloor a) m h D N).maxBits = 1 ∧
            ∀ (p : V → Fin N)
              (hx : feasible (ordinary G) (fun v => ((p v).val : ℝ) / D)),
              (nonintegerProgram (degreeFloor a) m h D N).runEncoded G p =
                fun v => decide (v ∈ nonintegerRounded G a ha hnoninteger
                  (fun u => ((p u).val : ℝ) / D) hx) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0 : ℚ) < a + 1 := by linarith
  obtain ⟨m, h, hm, hr⟩ := NoncriticalRationalParameters.natural_ratio
    (1 / (a + 1)) (div_pos zero_lt_one hap).le
  have hratio : (h : ℝ) / m = 1 / ((a : ℝ) + 1) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add] using hr
  refine ⟨m, h, hm, hratio, ?_, ?_⟩
  · intro V _ _ G _ hden
    have ht0 := theta_pos a ha hnoninteger
    have ht1 := theta_lt_one a ha hnoninteger
    have hdecomp := noninteger_decomposition a
    have hδ : 0 < (delta a : ℝ) := by
      rw [← delta_eq a]
      unfold CurrentNonintegerSlack.delta
      exact lt_min
        (div_pos (sub_pos.mpr ht1) (mul_pos (by linarith) (by linarith)))
        (div_pos ht0 (by positivity))
    obtain ⟨hleast, hvalue⟩ :=
      CurrentNonintegerTransformation.endpoint_transformed_optimum G (a : ℝ) haR
    refine ⟨hδ, hleast, hvalue, ?_⟩
    intro x hx
    dsimp only
    have hdom := CurrentNonintegerTransformation.universal_dominates G (a : ℝ) haR
      (degreeFloor a) (theta a : ℝ) hdecomp ht0 ht1 x hx
    have hs := CurrentNonintegerTransformation.universal_slack G (a : ℝ) haR
      (degreeFloor a) (theta a : ℝ) hdecomp ht0 ht1 hden x hx
    rw [delta_eq a] at hs
    have hslack : (1 + (delta a : ℝ)) *
        (nonintegerRounded G a ha hnoninteger x hx).card ≤
        CurrentNonintegerTransformation.transformedCost G (2 * (a : ℝ) + 1) x := by
      change (1 + (delta a : ℝ)) *
        (CurrentNonintegerTransformation.rounded G (a : ℝ) haR (degreeFloor a)
          (theta a : ℝ) hdecomp ht0 ht1 x hx).card ≤ _
      linarith
    exact ⟨hdom, hslack, fun hc => Slack.pays_for_error hδ hslack hc⟩
  · intro D N hD V _ _ G _
    refine ⟨noninteger_rounds _ _ _ _ _, noninteger_maxBits _ _ _ _ _, ?_⟩
    intro p hx
    exact noninteger_encoded_correct G a ha hnoninteger m h D N hm hD hratio p hx

end Paper.CurrentTheoremB
