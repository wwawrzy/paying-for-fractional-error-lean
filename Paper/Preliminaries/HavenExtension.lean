import Paper.Preliminaries.HavenGrow
import Paper.Preliminaries.ComponentContainment

/-! Enlarge one old branch to an actual deletion component avoiding the
new haven region and every other old branch. -/
namespace Paper.HavenExtension
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig DeletionComponents
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem union_budget {h r : ℕ} {H : Haven G (h * r)} {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (hless : C.card < h) (Z : Finset V) (hZ : Z.card ≤ r) :
    (X ∪ Z).card ≤ h * r := by
  have hc := Finset.card_union_le X Z
  have hx := HavenGrow.cover_bound good
  have hm := Nat.mul_le_mul_right r (show C.card + 1 ≤ h by omega)
  nlinarith

noncomputable def replacementX (X S Z T : Finset V) : Finset V := (Z ∩ T) ∪ (X \ S)

theorem replacement_subset (X S Z T : Finset V) : replacementX X S Z T ⊆ X ∪ Z := by
  intro v hv
  rcases Finset.mem_union.mp hv with hz | hx
  · exact Finset.mem_union_right _ (Finset.mem_inter.mp hz).1
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1

theorem exists_extension {h r : ℕ} (H : Haven G (h * r)) {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (hless : C.card < h) (Z : Finset V) (hZ : Z.card ≤ r)
    (S : Finset V) (hS : S ∈ C) :
    ∃ T : Finset V, S ⊆ T ∧ (G.induce (T : Set V)).Connected ∧
      Disjoint T (H.region (X ∪ Z) ∪ vertices (C.erase S)) ∧
      ∀ u ∈ T, ∀ v, v ∉ H.region (X ∪ Z) ∪ vertices (C.erase S) → G.Adj u v → v ∈ T := by
  classical
  have hY := union_budget good hless Z hZ
  have hm := H.monotone X (X ∪ Z) good.sizeX hY Finset.subset_union_left
  let F := H.region (X ∪ Z) ∪ vertices (C.erase S)
  have hdis : Disjoint S F := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvF
    rcases Finset.mem_union.mp hvF with hvB | hvC
    · exact Finset.disjoint_left.mp (good.separate S hS) hvS (hm hvB)
    · obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hvC
      have hh := Finset.mem_erase.mp hU
      exact Finset.disjoint_left.mp (good.covey.disjoint S hS U hh.2 (Ne.symm hh.1)) hvS hvU
  obtain ⟨u, huS⟩ := Covey.nonempty G good.covey hS
  have huF : u ∉ F := fun h => Finset.disjoint_left.mp hdis huS h
  let K := (deleted G F).connectedComponentMk ⟨u, huF⟩
  let T := physical G F K
  have hST : S ⊆ T := ComponentContainment.subset G F K S (good.covey.connected S hS) hdis
    ⟨u, Finset.mem_inter.mpr ⟨huS, DeletionComponents.covers G F huF⟩⟩
  exact ⟨T, hST, DeletionComponents.connected G F K, DeletionComponents.avoids G F K,
    fun _ hu _ hv ha => DeletionComponents.closed G F K hu hv ha⟩
end Paper.HavenExtension
