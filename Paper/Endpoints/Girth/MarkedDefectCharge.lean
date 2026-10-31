import Paper.Endpoints.Girth.MarkedRestriction
import Paper.Preliminaries.MinorDensity

/-! A marked planar graph charges exceptional degree units by the unmarked
low vertices and independent marked centers. -/
namespace Paper.MarkedDefectCharge
open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem bound (hplanar : G.IsPlanar) (A Q L B : Finset V)
    (hAT : Disjoint A (Q∪L)) (hQL : Disjoint Q L)
    (hA : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) (hB : B ⊆ Q)
    (g d : ℕ) (hg : 3 ≤ g)
    (hd : (d:ℝ) = 2*((g:ℝ)/((g:ℝ)-2)))
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v), c.IsCycle → g ≤ c.length)
    (hQ : ∀ q ∈ Q, d ≤ G.inducedDegree q (Q∪L))
    (hlower : ∀ q ∈ Q, d+(if q ∈ B then 1 else 0) ≤
      ((A∪(Q∪L)).filter (G.Adj q)).card) :
    (B.card:ℝ) ≤ (g:ℝ)*(A.card+L.card) := by
  let a : ℝ := (g:ℝ)/((g:ℝ)-2)
  let β : ℝ := ((g:ℝ)-3)/((g:ℝ)-2)
  have hgR : (3:ℝ) ≤ g := by exact_mod_cast hg
  have hpos : (0:ℝ) < (g:ℝ)-2 := by linarith
  have hβ : 0 ≤ β := div_nonneg (by linarith) hpos.le
  have hp := MarkedRestriction.crossing_bound G hplanar A Q L hAT hQL hA g d hg hd hgirth hQ
  have hf := MarkedRestriction.localized_face_bound G hplanar A (Q∪L) hAT hA g hg hgirth
  rw [Finset.card_union_of_disjoint hQL] at hf
  push_cast at hf
  have heQ := MarkedRestriction.induced_density_outside G hplanar A Q
    (hAT.mono_right Finset.subset_union_left) g hg hgirth
  have hn : d*Q.card+B.card ≤ (G.interedges Q (A∪(Q∪L))).card := by
    rw [Incidence.card_interedges_eq_sum]
    calc
      _ = ∑ q ∈ Q, (d+if q ∈ B then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.inter_eq_right.mpr hB,mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlower
  have hu := Incidence.card_interedges_le G Q (A∪(Q∪L))
  have hsub : Q ⊆ A∪(Q∪L) := fun q hq => Finset.mem_union_right _ (Finset.mem_union_left _ hq)
  rw [Finset.union_eq_right.mpr hsub,Finset.inter_eq_left.mpr hsub] at hu
  have huR : ((G.interedges Q (A∪(Q∪L))).card:ℝ) ≤
      G.inducedEdgeCount (A∪(Q∪L))+G.inducedEdgeCount Q := by exact_mod_cast hu
  have hnR : (d:ℝ)*Q.card+B.card ≤ (G.interedges Q (A∪(Q∪L))).card := by exact_mod_cast hn
  rw [hd] at hnR
  have hbp := mul_le_mul_of_nonneg_left hp hβ
  have hid : a+β*(g:ℝ) = g := by
    dsimp [a,β]
    field_simp
    ring
  change (G.inducedEdgeCount (A∪(Q∪L)):ℝ) ≤ a*(A.card+(Q.card+L.card))+
    β*(G.interedges A (Q∪L)).card at hf
  change (G.inducedEdgeCount Q:ℝ) ≤ a*Q.card at heQ
  change (2*a)*Q.card+B.card ≤ _ at hnR
  have hb : (B.card:ℝ) ≤ a*(A.card+L.card)+β*((g:ℝ)*(A.card+L.card)) := by
    nlinarith only [huR,hnR,hf,heQ,hbp]
  calc
    _ ≤ a*(A.card+L.card)+β*((g:ℝ)*(A.card+L.card)) := hb
    _ = (a+β*(g:ℝ))*(A.card+L.card) := by ring
    _ = _ := by rw [hid]

end Paper.MarkedDefectCharge
#print axioms Paper.MarkedDefectCharge.bound
