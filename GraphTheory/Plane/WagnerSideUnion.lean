import GraphTheory.Plane.WagnerSeparatorSides

/-!
# Domination and cardinality interfaces for actual side unions

These lemmas connect the exact graph produced by gluing the two side maps
back to the original graph, and discharge the small cardinality branches
of the final induction using only genuine set-separation data.
-/

namespace PlaneTopology.WagnerSideUnion

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Every original edge lies entirely in at least one side, so the actual
union of mapped side supergraphs really contains the original graph. -/
theorem original_le_sideUnion (A B : Set V)
    (hcover : A ∪ B = Set.univ)
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (L : SimpleGraph A) (R : SimpleGraph B)
    (hL : G.induce A ≤ L) (hR : G.induce B ≤ R) :
    G ≤ L.map Subtype.val ⊔ R.map Subtype.val := by
  intro x y hxy
  have hboth : (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
    have hx : x ∈ A ∨ x ∈ B := by
      change x ∈ A ∪ B
      rw [hcover]
      trivial
    have hy : y ∈ A ∨ y ∈ B := by
      change y ∈ A ∪ B
      rw [hcover]
      trivial
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · exact Or.inl ⟨hxA, hyA⟩
      · have hyB := hy.resolve_left hyA
        by_cases hxB : x ∈ B
        · exact Or.inr ⟨hxB, hyB⟩
        · exact (hcross x ⟨hxA, hxB⟩ y ⟨hyB, hyA⟩ hxy).elim
    · have hxB := hx.resolve_left hxA
      by_cases hyB : y ∈ B
      · exact Or.inr ⟨hxB, hyB⟩
      · have hyA := hy.resolve_right hyB
        exact (hcross y ⟨hyA, hyB⟩ x ⟨hxB, hxA⟩ hxy.symm).elim
  rcases hboth with ⟨hxA, hyA⟩ | ⟨hxB, hyB⟩
  · refine Or.inl ⟨hxy.ne, ⟨x, hxA⟩, ⟨y, hyA⟩, ?_, rfl, rfl⟩
    exact hL hxy
  · refine Or.inr ⟨hxy.ne, ⟨x, hxB⟩, ⟨y, hyB⟩, ?_, rfl, rfl⟩
    exact hR hxy

/-- A private left vertex gives one vertex beyond the entire separator. -/
theorem separator_card_add_one_le_left [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hA : (A \ B).Nonempty) :
    Nat.card S + 1 ≤ Nat.card A := by
  obtain ⟨a, haA, haB⟩ := hA
  have hanot : a ∉ A ∩ B := fun h => haB h.2
  have hsub : insert a (A ∩ B) ⊆ A := by
    intro x hx
    rcases hx with rfl | hx
    · exact haA
    · exact hx.1
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hanot, hinter] at hcard
  exact hcard

/-- A private right vertex likewise lies beyond the separator. -/
theorem separator_card_add_one_le_right [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hB : (B \ A).Nonempty) :
    Nat.card S + 1 ≤ Nat.card B :=
  separator_card_add_one_le_left B A S (by rw [Set.inter_comm, hinter]) hB

/-- A nonempty separator and a private left vertex force two left vertices. -/
theorem two_le_card_left [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hS : S.Nonempty) (hA : (A \ B).Nonempty) :
    2 ≤ Nat.card A := by
  have hsep : 0 < Nat.card S := hS.ncard_pos
  have hcard := separator_card_add_one_le_left A B S hinter hA
  omega

/-- The symmetric lower bound for the right side. -/
theorem two_le_card_right [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hS : S.Nonempty) (hB : (B \ A).Nonempty) :
    2 ≤ Nat.card B := by
  have hsep : 0 < Nat.card S := hS.ncard_pos
  have hcard := separator_card_add_one_le_right A B S hinter hB
  omega

/-- With a two-vertex separator the left side has at least three vertices. -/
theorem three_le_card_left [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hS : Nat.card S = 2) (hA : (A \ B).Nonempty) :
    3 ≤ Nat.card A := by
  have hcard := separator_card_add_one_le_left A B S hinter hA
  omega

/-- The symmetric three-vertex bound for a two-vertex separator. -/
theorem three_le_card_right [Finite V] (A B S : Set V)
    (hinter : A ∩ B = S) (hS : Nat.card S = 2) (hB : (B \ A).Nonempty) :
    3 ≤ Nat.card B := by
  have hcard := separator_card_add_one_le_right A B S hinter hB
  omega

/-- If the disjoint right side is a singleton, its actual vertex is outside
the left side, covers its complement, and has no original edge into it. -/
theorem singleton_right_of_separation (A B : Set V)
    (hcover : A ∪ B = Set.univ) (hinter : A ∩ B = ∅)
    (hcross : ∀ a ∈ A \ B, ∀ b ∈ B \ A, ¬G.Adj a b)
    (hB : Nat.card B = 1) :
    ∃ b : V, b ∉ A ∧ A ∪ {b} = Set.univ ∧ ∀ a ∈ A, ¬G.Adj b a := by
  obtain ⟨b, huniq⟩ := Nat.card_eq_one_iff_exists.mp hB
  have hBset : B = {b.val} := by
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val (huniq ⟨x, hx⟩)
    · intro hx
      change x = b.val at hx
      exact hx.symm ▸ b.property
  have hbA : b.val ∉ A := by
    intro hbA
    have hfalse : b.val ∈ (∅ : Set V) := hinter ▸ ⟨hbA, b.property⟩
    exact hfalse
  refine ⟨b.val, hbA, ?_, ?_⟩
  · rw [← hBset]
    exact hcover
  · intro a ha hba
    have haB : a ∉ B := by
      intro haB
      have hfalse : a ∈ (∅ : Set V) := hinter ▸ ⟨ha, haB⟩
      exact hfalse
    exact hcross a ⟨ha, haB⟩ b.val ⟨b.property, hbA⟩ hba.symm

#print axioms original_le_sideUnion
#print axioms separator_card_add_one_le_left
#print axioms singleton_right_of_separation

end PlaneTopology.WagnerSideUnion
