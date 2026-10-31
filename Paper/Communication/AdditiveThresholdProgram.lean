import Paper.Endpoints.Rounding.AdditiveThresholdCount
import Paper.Communication.ObserveProgram

/-! A single physical one-bit broadcast for fv:imp:additive. Only the local
threshold flag is sent; no coordinate or neighborhood list is communicated. -/
namespace Paper.AdditiveThresholdProgram
open BroadcastModel SevenFoundation AdditiveThreshold
variable {V : Type} [DecidableEq V]

def flags : Program V Bool Bool :=
  ObserveProgram.program id (fun _ selected seen => selected || decide (seen = ∅))

noncomputable def program (t : ℝ) : Program V ℝ Bool := by
  classical
  exact .seq (.local fun _ _ xv => decide (t ≤ xv)) flags

theorem rounds (t : ℝ) : (program (V := V) t).rounds = 1 := rfl
theorem maxBits (t : ℝ) : (program (V := V) t).maxBits = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (t : ℝ) (x : V → ℝ) :
    (program t).run G x = fun v => decide (v ∈ AdditiveThreshold.output G t x) := by
  classical
  change flags.run G (fun v => decide (t ≤ x v)) = _
  have hf : (fun v => id (decide (t ≤ x v))) = fun v => decide (v ∈ AdditiveThreshold.first G t x) := by
    funext v
    simp [AdditiveThreshold.first]
  rw [flags,ObserveProgram.run G id _ _ (AdditiveThreshold.first G t x) hf]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,AdditiveThreshold.output,AdditiveThreshold.residual,Finset.mem_union,
    Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [← not_iff_not]
  simp only [not_or,not_le,not_not]
  have hseen := ClosedBitProgram.covered_iff G (AdditiveThreshold.first G t x) v
  simp only [Finset.nonempty_iff_ne_empty] at hseen
  simp only [AdditiveThreshold.first,Finset.mem_filter,Finset.mem_univ,true_and] at *
  simp only [not_le]
  exact and_congr Iff.rfl hseen

theorem endpoint (a η : ℝ) (ha : 0 < a) (hη : 0 ≤ η)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ a*S.card+η) :
    dominates G (AdditiveThreshold.output G (1/(2*a+1)) x) ∧
    ((AdditiveThreshold.output G (1/(2*a+1)) x).card : ℝ) ≤ (2*a+1)*(∑ v, x v)+2*η/a ∧
    ((program (1/(2*a+1))).run G x = fun v => decide (v ∈ AdditiveThreshold.output G (1/(2*a+1)) x)) ∧
    (program (V := V) (1/(2*a+1))).rounds = 1 ∧
    (program (V := V) (1/(2*a+1))).maxBits = 1 :=
  ⟨dominates_output G _ x,output_bound G a η ha hη x hx hden,
    correct G _ x,rounds _,maxBits _⟩

end Paper.AdditiveThresholdProgram
#print axioms Paper.AdditiveThresholdProgram.correct
#print axioms Paper.AdditiveThresholdProgram.endpoint
