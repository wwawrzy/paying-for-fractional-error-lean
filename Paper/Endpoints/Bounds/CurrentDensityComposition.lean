import Paper.Endpoints.Bounds.CurrentDensityFromFractional

/-! Composition of an external encoded fractional program with the exact
current noninteger rounding. The external program and its guarantees remain
explicit parameters; no external algorithm is postulated as an axiom. -/

namespace Paper.CurrentDensityComposition
open BroadcastModel SevenFoundation CurrentTheoremB
open scoped BigOperators

variable {V In : Type} [DecidableEq V]

def program (k m h D N : ℕ) (P : Program V In (Fin N)) : Program V In Bool :=
  .seq P (nonintegerProgram k m h D N)

theorem rounds (k m h D N : ℕ) (P : Program V In (Fin N)) :
    (program k m h D N P).rounds = P.rounds + 3 := rfl

theorem maxBits (k m h D N : ℕ) (P : Program V In (Fin N)) :
    (program k m h D N P).maxBits = max P.maxBits 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output (k m h D N : ℕ) (P : Program V In (Fin N)) (s : V → In) : Finset V :=
  Finset.univ.filter (fun v => (program k m h D N P).runEncoded G s v)

/-- The composed executable returns exactly the capped mathematical rounding. -/
theorem output_eq (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (hratio : (h : ℝ) / m = 1 / ((a : ℝ) + 1))
    (P : Program V In (Fin N)) (s : V → In)
    (hx : feasible (ordinary G) (fun v => ((P.runEncoded G s v).val : ℝ) / D)) :
    output G (degreeFloor a) m h D N P s =
      nonintegerRounded G a ha hnoninteger
        (fun v => ((P.runEncoded G s v).val : ℝ) / D) hx := by
  have he := noninteger_encoded_correct G a ha hnoninteger m h D N hm hD hratio
    (P.runEncoded G s) hx
  ext v
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [program, Program.runEncoded]
  rw [congrFun he v]
  simp only [decide_eq_true_eq]

/-- Feasibility and the external objective bound suffice for the exact
coefficient. The communication overhead is three one-bit broadcasts. -/
theorem exact_bound (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (hden : Incidence.InducedDensityBound G (a : ℝ))
    (m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (hratio : (h : ℝ) / m = 1 / ((a : ℝ) + 1))
    (P : Program V In (Fin N)) (s : V → In)
    (hx : feasible (ordinary G) (fun v => ((P.runEncoded G s v).val : ℝ) / D))
    (hsolver : (∑ v, ((P.runEncoded G s v).val : ℝ) / D) ≤
      (1 + (delta a : ℝ)) * fractionalNumber G) :
    dominates G (output G (degreeFloor a) m h D N P s) ∧
      ((output G (degreeFloor a) m h D N P s).card : ℝ) ≤
        (2 * (a : ℝ) + 1) * fractionalNumber G := by
  rw [output_eq G a ha hnoninteger m h D N hm hD hratio P s hx]
  exact CurrentDensityFromFractional.output_bound G a ha hnoninteger hden _ hx hsolver

end Paper.CurrentDensityComposition

#print axioms Paper.CurrentDensityComposition.rounds
#print axioms Paper.CurrentDensityComposition.maxBits
#print axioms Paper.CurrentDensityComposition.output_eq
#print axioms Paper.CurrentDensityComposition.exact_bound
