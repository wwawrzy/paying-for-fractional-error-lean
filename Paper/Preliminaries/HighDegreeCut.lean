import Paper.Preliminaries.MinorDensity

/-! Count high-degree owner vertices by handshaking and bound the degree
of the actual induced graph after removing them. -/
namespace Paper.HighDegreeCut
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def high (Δ : ℕ) : Finset V := Finset.univ.filter (fun v => Δ < G.degree v)

theorem count (Δ : ℕ) {a : ℝ} (hden : (G.edgeFinset.card : ℝ) ≤ a * Fintype.card V) :
    (Δ : ℝ) * (high G Δ).card ≤ 2 * a * Fintype.card V := by
  have hlo : Δ * (high G Δ).card ≤ ∑ v ∈ high G Δ, G.degree v := by
    calc
      _ = ∑ _v ∈ high G Δ, Δ := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => by have hh := (Finset.mem_filter.mp hv).2; omega)
  have hsum : (∑ v ∈ high G Δ, G.degree v) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hh := hlo.trans hsum
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hh
  have hr : (Δ : ℝ) * (high G Δ).card ≤ 2 * (G.edgeFinset.card : ℝ) := by exact_mod_cast hh
  linarith

noncomputable def pruned (Δ : ℕ) : SimpleGraph {v // v ∉ high G Δ} :=
  G.induce {v | v ∉ high G Δ}

theorem degree_bound (Δ : ℕ) (v : {v // v ∉ high G Δ}) : (pruned G Δ).degree v ≤ Δ := by
  classical
  have hn : ¬ Δ < G.degree v.val := fun h => v.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hc := Finset.card_le_card_of_injOn (fun u : {v // v ∉ high G Δ} => u.val)
    (s := (pruned G Δ).neighborFinset v) (t := G.neighborFinset v.val)
    (fun u hu => (G.mem_neighborFinset _ _).mpr (((pruned G Δ).mem_neighborFinset _ _).mp hu))
    (fun _ _ _ _ h => Subtype.ext h)
  change (pruned G Δ).degree v ≤ G.degree v.val at hc
  omega
end Paper.HighDegreeCut
