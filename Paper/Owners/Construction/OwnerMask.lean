import Paper.Owners.Construction.OwnerSampleMinor

/-! Restrict the finite owner experiment to any specified owner set. This
is needed for induced density, rather than only a global edge count. -/
namespace Paper.OwnerMask
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerExperiment
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def mask (I : Finset V) {L : ℕ} (hL : 1 ≤ L)
    (ω : V ⊕ V → Fin (L + 1)) : V ⊕ V → Fin (L + 1)
  | .inl d => if d ∈ I then ω (.inl d) else ⟨1, by omega⟩
  | .inr v => ω (.inr v)

theorem sampled_subset (D I : Finset V) {L : ℕ} (hL : 1 ≤ L) (ω : V ⊕ V → Fin (L + 1)) :
    sampled D (mask I hL ω) ⊆ I := by
  intro d hd
  have hz := (Finset.mem_filter.mp hd).2
  by_contra hn
  simp [mask, hn] at hz

theorem density (D R I : Finset V) {L : ℕ} (hL : 1 ≤ L) (ω : V ⊕ V → Fin (L + 1))
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    ((OwnerExperiment.graph G D R L (mask I hL ω)).edgeFinset.card : ℝ) ≤ a * I.card := by
  classical
  have hh := hden (sampled D (mask I hL ω)) (OwnerExperiment.graph G D R L (mask I hL ω))
    ⟨OwnerSampleMinor.model G D R L _⟩
  have hc : Fintype.card (sampled D (mask I hL ω)) ≤ I.card := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (sampled_subset D I hL ω)
  have hc' : (Fintype.card (sampled D (mask I hL ω)) : ℝ) ≤ I.card := by exact_mod_cast hc
  exact hh.trans (mul_le_mul_of_nonneg_left hc' ha)
end Paper.OwnerMask
