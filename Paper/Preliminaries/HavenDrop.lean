import Paper.Preliminaries.HavenConfig

/-! A branch untouched by X can be dropped from the original configuration,
strictly decreasing its actual potential. -/
namespace Paper.HavenDrop
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem drop {h r : ℕ} (H : Haven G (h * r)) {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (S : Finset V) (hS : S ∈ C) (hzero : (X ∩ S).card = 0) :
    Good h r H (C.erase S) X ∧ score H (C.erase S) X < score H C X := by
  classical
  have hdis : Disjoint X S := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hcard := Finset.card_erase_add_one hS
  have hgood : Good h r H (C.erase S) X := by
    refine ⟨Covey.erase G good.covey S, by have hh := good.card; omega, ?_, ?_, ?_⟩
    · intro v hvX
      obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp (good.cover hvX)
      have hUS : U ≠ S := fun he => Finset.disjoint_left.mp hdis hvX (he ▸ hvU)
      exact Finset.mem_biUnion.mpr ⟨U, Finset.mem_erase.mpr ⟨hUS, hU⟩, hvU⟩
    · intro U hU
      exact good.overlap U (Finset.mem_of_mem_erase hU)
    · intro U hU
      exact good.separate U (Finset.mem_of_mem_erase hU)
  refine ⟨hgood, ?_⟩
  dsimp only [score]
  omega
end Paper.HavenDrop
