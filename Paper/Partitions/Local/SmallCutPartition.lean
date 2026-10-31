import Paper.Preliminaries.SmallParts
import Paper.Preliminaries.CrossingEdges

/-! A genuine connected small-part partition with a controlled number of
actual crossing edges, derived from induced separators and bounded degree. -/
namespace Paper.SmallCutPartition
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem deletion_edges (S D : Finset V) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    (CrossingEdges.graph G S (SmallParts.label G S D)).edgeFinset.card ≤ Δ * D.card := by
  apply CrossingEdges.count G S D _ Δ (fun v _ => hdeg v)
  intro u v ha
  by_cases hu : u ∈ D
  · exact Or.inl hu
  · right
    by_contra hv
    exact ha.2.2.2 (SmallParts.label_adj G S D u v
      (Finset.mem_sdiff.mpr ⟨ha.2.1, hu⟩) (Finset.mem_sdiff.mpr ⟨ha.2.2.1, hv⟩) ha.1)

theorem exists_partition {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (S : Finset V) :
    ∃ D : Finset V, D ⊆ S ∧ ∃ P : SmallParts.Data G S k,
      P.parts = S.image (SmallParts.label G S D) ∧
      ((CrossingEdges.graph G S (SmallParts.label G S D)).edgeFinset.card : ℝ) ≤
        (4 * Δ * C / Real.sqrt k) * S.card := by
  obtain ⟨D, hgood, hsize⟩ := RecursiveDeletion.exists_cut G hC hprofile k hk S
  refine ⟨D, hgood.1, SmallParts.of_cut G S D k hk hgood, rfl, ?_⟩
  have hb : ((CrossingEdges.graph G S (SmallParts.label G S D)).edgeFinset.card : ℝ) ≤
      (Δ : ℝ) * D.card := by exact_mod_cast deletion_edges G S D Δ hdeg
  have hs := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)
  calc
    _ ≤ (Δ : ℝ) * (4 * C / Real.sqrt k * S.card) := hb.trans hs
    _ = _ := by ring

theorem prescribed {C ε : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε) (S : Finset V) :
    ∃ D : Finset V, D ⊆ S ∧ ∃ P : SmallParts.Data G S k,
      P.parts = S.image (SmallParts.label G S D) ∧
      ((CrossingEdges.graph G S (SmallParts.label G S D)).edgeFinset.card : ℝ) ≤ ε * S.card := by
  obtain ⟨D, hD, P, he, hb⟩ := exists_partition G hC hprofile Δ hdeg k hk S
  exact ⟨D, hD, P, he, hb.trans (mul_le_mul_of_nonneg_right hparam (Nat.cast_nonneg _))⟩
end Paper.SmallCutPartition
