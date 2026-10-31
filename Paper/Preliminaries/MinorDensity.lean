import Paper.Preliminaries.StarMinor
import Paper.Preliminaries.Incidence

/-! Density of actual simple minors, with the real parameter unchanged. -/
namespace Paper.MinorDensity
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The paper's structural input: every finite simple minor has density ≤t. -/
def Bound (t : ℝ) : Prop :=
  ∀ (A : Type u) [Fintype A] [DecidableEq A] (J : SimpleGraph A)
    [DecidableRel J.Adj], SimpleGraph.IsMinor J G →
      (J.edgeFinset.card : ℝ) ≤ t * Fintype.card A

theorem induced_bound {t : ℝ} (h : Bound G t) : Incidence.InducedDensityBound G t := by
  classical
  intro S
  have hb := h (S : Set V) (G.induce (S : Set V)) (SimpleGraph.IsMinor.of_induce G _)
  simpa only [SimpleGraph.inducedEdgeCount, Fintype.card_eq_nat_card,
    Finset.coe_sort_coe, Nat.card_eq_finsetCard] using hb

theorem minor_induced_bound {A : Type u} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] {t : ℝ}
    (h : Bound G t) (hm : SimpleGraph.IsMinor J G) :
    Incidence.InducedDensityBound J t := by
  classical
  intro S
  have hb := h (S : Set A) (J.induce (S : Set A))
    ((SimpleGraph.IsMinor.of_induce J _).trans hm)
  simpa only [SimpleGraph.inducedEdgeCount, Fintype.card_eq_nat_card,
    Finset.coe_sort_coe, Nat.card_eq_finsetCard] using hb

/-- A lower bound on the induced degree of every q charges one distinct
unit for each exceptional q. Internal Q edges are counted a second time. -/
theorem charged_card_le {t : ℝ} (hden : Incidence.InducedDensityBound G t)
    (d : ℕ) (hd : (d : ℝ) = 2 * t) (Q X B : Finset V)
    (hdis : Disjoint Q X) (hB : B ⊆ Q)
    (hlower : ∀ q ∈ Q,
      d + (if q ∈ B then 1 else 0) ≤ ((Q ∪ X).filter (G.Adj q)).card) :
    (B.card : ℝ) ≤ t * X.card := by
  classical
  have hn : d * Q.card + B.card ≤ (G.interedges Q (Q ∪ X)).card := by
    rw [Incidence.card_interedges_eq_sum]
    calc
      d * Q.card + B.card = ∑ q ∈ Q, (d + if q ∈ B then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        have hi : Q.filter (fun q => q ∈ B) = B := by
          ext q
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
        simp [Finset.inter_eq_right.mpr hB, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlower
  have hu := Incidence.card_interedges_le G Q (Q ∪ X)
  rw [Finset.union_eq_right.mpr Finset.subset_union_left,
    Finset.inter_eq_left.mpr Finset.subset_union_left] at hu
  have hu' : ((G.interedges Q (Q ∪ X)).card : ℝ) ≤
      (G.inducedEdgeCount (Q ∪ X) : ℝ) + G.inducedEdgeCount Q := by exact_mod_cast hu
  have hn' : (d : ℝ) * Q.card + B.card ≤ (G.interedges Q (Q ∪ X)).card := by
    exact_mod_cast hn
  have hQ := hden Q
  have hX := hden (Q ∪ X)
  rw [Finset.card_union_of_disjoint hdis] at hX
  push_cast at hX
  rw [hd] at hn'
  nlinarith
end Paper.MinorDensity
