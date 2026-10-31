import Paper.RedBlue.IncidenceDensity
import Paper.Endpoints.Rounding.CoveringApproximateRounding

/-! Planar red-blue rounding on the actual neighborhood rows. The fractional
input guarantee remains explicit until composition with the covering solver. -/
namespace Paper.RedBlue
open BroadcastModel SevenFoundation CoveringThresholdInput
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def roundingInput {M : ℕ} (R B : Finset V) (c : V → Fin (M + 1))
    (n : V → ℕ) (v : V) : Input V M :=
  ⟨decide (v ∈ R), c v, rows G R B v, n v⟩

theorem rounding_rows {M : ℕ} (R B : Finset V) (c : V → Fin (M + 1))
    (n : V → ℕ) :
    CoveringThresholdCost.rows (roundingInput G R B c n) = rows G R B := by
  funext r
  by_cases hr : r ∈ R <;>
    simp [CoveringThresholdCost.rows, GeneralCoveringRounding.normalize,
      CoveringThresholdCost.demands, roundingInput, rows, hr]

theorem rounding_cost {b M : ℕ} (ids : BitCode V b)
    (hp : G.IsPlanar) (R B : Finset V) (hRB : Disjoint R B)
    (c : V → Fin (M + 1)) (n : V → ℕ) (q : ℕ) (hq : 0 < q)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ rows G R B r, (n v : ℝ) / q)
    (τ ε : ℝ)
    (happrox : (∑ v, (c v).val * ((n v : ℝ) / q)) ≤ (1 + ε / 4) * τ) :
    (∑ v ∈ CoveringThresholdCost.output G ids 4 q (roundingInput G R B c n),
      ((c v).val : ℝ)) ≤ (4 + ε) * τ := by
  have hl : ∀ r, (roundingInput G R B c n r).demand = true →
      (roundingInput G R B c n r).candidates ⊆ closed G r :=
    fun r _ => rows_local G R B r
  have hn : ∀ r, (roundingInput G R B c n r).demand = true →
      (roundingInput G R B c n r).candidates.Nonempty := by
    intro r hr
    exact hne r (by simpa [roundingInput] using hr)
  have hd := planar_density G hp R B hRB
  rw [← rounding_rows G R B c n] at hd
  have hc : ∀ r, (roundingInput G R B c n r).demand = true →
      1 ≤ ∑ v ∈ (roundingInput G R B c n r).candidates,
        CoveringThresholdCost.vector q (roundingInput G R B c n) v := by
    intro r hr
    exact hcover r (by simpa [roundingInput] using hr)
  simpa [CoveringThresholdCost.cost, CoveringThresholdCost.vector, roundingInput, show (2 : ℝ) * 2 = 4 by norm_num] using
    CoveringApproximateRounding.open_bound G ids 2 q (by decide) hq
      (roundingInput G R B c n) hl hn hd (fun r _ => no_self G R B r) hc τ ε
      (by simpa [CoveringThresholdCost.cost, CoveringThresholdCost.vector,
        roundingInput, show (2 : ℝ) * 2 = 4 by norm_num] using happrox)

end Paper.RedBlue
#print axioms Paper.RedBlue.rounding_rows
#print axioms Paper.RedBlue.rounding_cost


