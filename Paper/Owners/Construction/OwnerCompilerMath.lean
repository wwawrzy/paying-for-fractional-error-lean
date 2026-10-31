import Paper.Averaging.Tasks.CompilerFromLaw
import Paper.Owners.Construction.OwnerLocalPartition

/-! Construct the actual averaged fractional vector from physical minor
density, repairs, the proved finite partition law and actual task solvers.
This is the mathematical compiler; broadcast execution remains open. -/
namespace Paper.OwnerCompilerMath
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (hcover : R ⊆ covered G D) (L Δ : ℕ) (hL : 1 ≤ L)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
    (ξ η : ℝ) (hξ : 0 < ξ) (hη : 0 < η) :
    let Q := HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ
    ∃ x : V → ℝ, PartialOptimum.Feasible G R x ∧
      PartialOptimum.objective c x ≤ (1 + ξ) * PartialOptimum.number G R c +
        B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + 2 * η * D.card) := by
  classical
  dsimp only
  let Q := HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hh : 2 * (a : ℝ) + 1 < (2 * a + 2 : ℕ) := by push_cast; linarith
  have hb := OwnerLocalPartition.spec G D R L Δ hL hden ha0 (2 * a + 2) hh hη
  obtain ⟨law⟩ := FinitePartitionLaw.of_bound
    (HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ) Δ hb
  have law' : FinitePartitionLaw.Data (OwnerTasks.graph G D R L Q) η := law
  obtain ⟨x, hx, hxcost⟩ := CompilerFromLaw.spec G D R hcover L Q a ha hden c hc B₀ hB₀ hcost ξ hξ η law'
  refine ⟨x, hx, ?_⟩
  have hcardNat : Fintype.card (Low D Q) ≤ D.card := by
    have h := Fintype.card_le_of_injective (fun i : Low D Q => i.val) Subtype.val_injective
    simpa only [Fintype.card_coe] using h
  have hcard : (Fintype.card (Low D Q) : ℝ) ≤ D.card := by exact_mod_cast hcardNat
  have hm := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * η)
  have hm' := mul_le_mul_of_nonneg_left hm hB₀
  nlinarith
end Paper.OwnerCompilerMath
