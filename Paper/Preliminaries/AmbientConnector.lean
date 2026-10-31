import Paper.Preliminaries.FiniteConnector
import Paper.Preliminaries.InducedSubsets

/-! Connecting-set dichotomy within a specified actual physical region.
All outputs and the cut condition are transported back to physical vertices. -/
namespace Paper.AmbientConnector
attribute [local instance] Classical.propDecidable
open InducedSubsets
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem dichotomy {I : Type*} [Fintype I] (U : Finset V) (hU : U.Nonempty)
    (A : I → Finset V) (hA : ∀ i, A i ⊆ U) (r : ℕ) (hr : 1 ≤ r) :
    (∃ T : Finset V, T ⊆ U ∧ T.card ≤ r ∧ (G.induce (T : Set V)).Connected ∧ ∀ i, (T ∩ A i).Nonempty) ∨
      ∃ Z : Finset V, Z ⊆ U ∧ r * Z.card ≤ (Fintype.card I - 1) * U.card ∧
        ∀ C : Finset V, C ⊆ U → (G.induce (C : Set V)).Connected → Disjoint C Z →
          ¬ ∀ i, (C ∩ A i).Nonempty := by
  classical
  haveI : Nonempty ↥U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  let A' := fun i => lift U (A i)
  rcases FiniteConnector.dichotomy (G.induce (U : Set V)) A' r hr with ht | hz
  · left
    obtain ⟨T, hT, hc, hm⟩ := ht
    refine ⟨physical U T, physical_subset U T, ?_, physical_connected G U T hc, ?_⟩
    · simpa only [physical_card] using hT
    · intro i
      obtain ⟨v, hv⟩ := hm i
      have hv' := Finset.mem_inter.mp hv
      exact ⟨v.val, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v, hv'.1, rfl⟩,
        Finset.mem_subtype.mp hv'.2⟩⟩
  · right
    obtain ⟨Z, hZ, hcut⟩ := hz
    refine ⟨physical U Z, physical_subset U Z, ?_, ?_⟩
    · simpa only [physical_card, Finset.coe_sort_coe, Fintype.card_coe] using hZ
    · intro C hCU hconn hdis hmeet
      have hdis' : Disjoint (lift U C) Z := by
        apply Finset.disjoint_left.mpr
        intro v hvC hvZ
        exact Finset.disjoint_left.mp hdis (Finset.mem_subtype.mp hvC)
          (Finset.mem_image.mpr ⟨v, hvZ, rfl⟩)
      apply hcut (lift U C) (lift_connected G U C hCU hconn) hdis'
      intro i
      obtain ⟨v, hv⟩ := hmeet i
      have hv' := Finset.mem_inter.mp hv
      let u : U := ⟨v, hCU hv'.1⟩
      exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_subtype.mpr hv'.1, Finset.mem_subtype.mpr hv'.2⟩⟩
end Paper.AmbientConnector
