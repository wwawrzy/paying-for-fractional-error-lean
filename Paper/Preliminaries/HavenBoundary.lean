import Paper.Preliminaries.HavenExtension
import Paper.Preliminaries.LayeredConnector

/-! The boundary-crossing step in the second haven exchange. It proves
the new haven avoids the extended branch and stays in the old haven. -/
namespace Paper.HavenBoundary
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig HavenExtension
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
theorem avoids_extended {h r : ℕ} (H : Haven G (h * r)) {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (hless : C.card < h) (Z : Finset V) (hZ : Z.card ≤ r)
    (hZsub : Z ⊆ H.region X) (S : Finset V) (hS : S ∈ C) (T : Finset V) (hST : S ⊆ T)
    (hTF : Disjoint T (H.region (X ∪ Z) ∪ vertices (C.erase S)))
    (hclosed : ∀ u ∈ T, ∀ v, v ∉ H.region (X ∪ Z) ∪ vertices (C.erase S) → G.Adj u v → v ∈ T)
    (hcontact : ¬ Contacts G S (H.region (X ∪ Z))) :
    Disjoint (H.region (replacementX X S Z T)) (T ∪ (Finset.univ \ H.region X)) := by
  classical
  let Y := X ∪ Z
  let X' := replacementX X S Z T
  let W := T ∪ (Finset.univ \ H.region X)
  have hY : Y.card ≤ h * r := union_budget good hless Z hZ
  have hX' : X'.card ≤ h * r := (Finset.card_le_card (replacement_subset X S Z T)).trans hY
  have hBY : H.region Y ⊆ H.region X := H.monotone X Y good.sizeX hY Finset.subset_union_left
  have hBY' : H.region Y ⊆ H.region X' := H.monotone X' Y hX' hY (replacement_subset X S Z T)
  have hWBY : Disjoint W (H.region Y) := by
    apply Finset.disjoint_left.mpr
    intro v hvW hvB
    rcases Finset.mem_union.mp hvW with hvT | hvO
    · exact Finset.disjoint_left.mp hTF hvT (Finset.mem_union_left _ hvB)
    · exact (Finset.mem_sdiff.mp hvO).2 (hBY hvB)
  apply Finset.disjoint_left.mpr
  intro w hwNew hwW
  obtain ⟨q, hq⟩ := H.nonempty Y hY
  have hqNew := hBY' hq
  have hqW : q ∉ W := fun h => Finset.disjoint_left.mp hWBY h hq
  obtain ⟨p⟩ := H.connected X' hX' ⟨w, hwNew⟩ ⟨q, hqNew⟩
  obtain ⟨u, _, v, _, hadj, huW, hvW⟩ := LayeredConnector.walk_cross_cut
    (G.induce (H.region X' : Set V)) (fun z => z.val ∈ W) p hwW hqW
  have ha : G.Adj u.val v.val := hadj
  have huNot : u.val ∉ X' := fun hx => Finset.disjoint_left.mp (H.avoids X' hX') u.property hx
  have hvBX : v.val ∈ H.region X := by
    by_contra hn
    exact hvW (Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))
  have hvNotT : v.val ∉ T := fun ht => hvW (Finset.mem_union_left _ ht)
  have huXS : u.val ∈ X → u.val ∈ S := by
    intro huX
    by_contra hn
    exact huNot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨huX, hn⟩))
  have huXB : u.val ∈ X ∨ u.val ∈ H.region X := by
    by_cases huX : u.val ∈ X
    · exact Or.inl huX
    · exact Or.inr (H.closed X good.sizeX v.val hvBX u.val huX ha.symm)
  have huT : u.val ∈ T := by
    rcases Finset.mem_union.mp huW with huT | huO
    · exact huT
    · have huNB := (Finset.mem_sdiff.mp huO).2
      have huX := huXB.resolve_right huNB
      exact hST (huXS huX)
  have hvF : v.val ∈ H.region Y ∪ vertices (C.erase S) := by
    by_contra hn
    exact hvNotT (hclosed u.val huT v.val hn ha)
  have hvBY : v.val ∈ H.region Y := by
    rcases Finset.mem_union.mp hvF with hvB | hvO
    · exact hvB
    · obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hvO
      exact False.elim (Finset.disjoint_left.mp (good.separate U (Finset.mem_of_mem_erase hU)) hvU hvBX)
  have huNotBY : u.val ∉ H.region Y := fun hb =>
    Finset.disjoint_left.mp hTF huT (Finset.mem_union_left _ hb)
  have huY : u.val ∈ Y := by
    by_contra hn
    exact huNotBY (H.closed Y hY v.val hvBY u.val hn ha.symm)
  have huX : u.val ∈ X := by
    rcases Finset.mem_union.mp huY with huX | huZ
    · exact huX
    · exact False.elim (huNot (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huZ, huT⟩)))
  exact hcontact ⟨u.val, huXS huX, v.val, hvBY, ha⟩
end Paper.HavenBoundary
