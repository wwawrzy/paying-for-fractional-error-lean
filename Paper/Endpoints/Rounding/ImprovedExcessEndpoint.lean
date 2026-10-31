import Paper.Endpoints.Rounding.ImprovedExcessProgram
import Paper.Endpoints.Rounding.ImprovedExcessRounding
import Paper.Communication.EncodedProgram

/-! The paper's rational density and gain instantiate the exact rounding
rule. The floor and fractional gap are computed from the density. The actual
encoded program uses three one-bit broadcasts on arbitrary private real inputs. -/
namespace Paper.ImprovedExcessEndpoint
open SevenFoundation BroadcastModel
open scoped BigOperators

noncomputable def cutoff (a : ℚ) : ℕ := Nat.floor (2 * (a : ℝ))
noncomputable def gap (a : ℚ) : ℝ := 2 * (a : ℝ) - (cutoff a : ℝ)

theorem gap_bounds (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    0 < gap a ∧ gap a < 1 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlo : (cutoff a : ℝ) ≤ 2 * (a : ℝ) := Nat.floor_le (by linarith)
  have hne : (cutoff a : ℝ) ≠ 2 * (a : ℝ) := by
    intro h
    apply hnoninteger
    refine ⟨(cutoff a : ℤ), ?_⟩
    exact_mod_cast h
  have hlt := lt_of_le_of_ne hlo hne
  have hhi : 2 * (a : ℝ) < (cutoff a : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold gap
  constructor <;> linarith

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def selected (k : ℕ) (threshold : ℝ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => (ImprovedExcessProgram.program k threshold).runEncoded G x v = true

theorem selected_eq (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    selected G k threshold x = ImprovedExcess.output G k threshold x := by
  unfold selected
  rw [Program.runEncoded_eq_run, ImprovedExcessProgram.correct]
  ext v
  simp

/-- Exact rational-parameter form of `fv:imp:lemma`, including its stated
three Boolean broadcasts. The caller chooses the admissible gain, also zero. -/
theorem rounding (a μ : ℚ) (η : ℝ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (hμ : 0 ≤ μ) (hμθ : (μ : ℝ) ≤ gap a) (hη : 0 ≤ η)
    (hadm : ((μ : ℝ) + 1) * ((μ : ℝ) + 1 - gap a) ≤
      (2 * (a : ℝ) + 1) * (1 - gap a) / (a : ℝ))
    (hden : ImprovedExcess.DensityWithExcess G (a : ℝ) η)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x)
    (hcap : ∀ v, x v ≤ 1) :
    let t := ImprovedExcess.threshold (a : ℝ) (gap a) (μ : ℝ)
    dominates G (selected G (cutoff a) t x) ∧
      ((selected G (cutoff a) t x).card : ℝ) ≤
        (2 * (a : ℝ) + 1 - (μ : ℝ)) * (∑ v, x v) +
          2 * η * t * (1 + (μ : ℝ) / (1 - gap a)) ∧
      (ImprovedExcessProgram.program (V := V) (cutoff a) t).rounds = 3 ∧
      (ImprovedExcessProgram.program (V := V) (cutoff a) t).maxBits = 1 := by
  obtain ⟨hθ, hθ1⟩ := gap_bounds a ha hnoninteger
  have heq : 2 * (a : ℝ) = (cutoff a : ℝ) + gap a := by unfold gap; ring
  have h := ImprovedExcess.improved_rounding G (a : ℝ) (gap a) (μ : ℝ) η
    (by exact_mod_cast ha) hθ hθ1 (by exact_mod_cast hμ) hμθ hη hadm
    (cutoff a) heq hden x hx hcap
  dsimp only
  rw [selected_eq]
  exact ⟨h.1, h.2, ImprovedExcessProgram.rounds _ _, ImprovedExcessProgram.maxBits _ _⟩

end Paper.ImprovedExcessEndpoint

#print axioms Paper.ImprovedExcessEndpoint.gap_bounds
#print axioms Paper.ImprovedExcessEndpoint.selected_eq
#print axioms Paper.ImprovedExcessEndpoint.rounding
