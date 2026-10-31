import GraphTheory.SimpleGraph.Minor.ContractibleEdge

/-!
# Actual finite separation for the remaining Wagner induction

A disconnected graph after deletion of a small separator gives two proper
vertex sides whose only overlap is that separator and with no crossing
edge. The construction uses one actual reachability class of the residual
graph; the smaller cardinalities are proved, not carried as assumptions.
-/

namespace PlaneTopology.WagnerSeparation

open SimpleGraph SimpleGraph.EdgeContraction

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The concrete two sides of a graph separation. Each side has a vertex
outside the other, so neither side can equal the whole vertex set. -/
structure Separation (S : Finset V) where
  left : Set V
  right : Set V
  cover : left ∪ right = Set.univ
  overlap : left ∩ right = (S : Set V)
  left_private : (left \ right).Nonempty
  right_private : (right \ left).Nonempty
  no_cross : ∀ x ∈ left \ right, ∀ y ∈ right \ left, ¬G.Adj x y

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The left side is genuinely smaller than the original finite vertex type. -/
theorem Separation.card_left_lt {S : Finset V} (s : Separation G S) :
    Nat.card s.left < Fintype.card V := by
  classical
  obtain ⟨y, _, hy⟩ := s.right_private
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hy

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The right side is genuinely smaller as well. -/
theorem Separation.card_right_lt {S : Finset V} (s : Separation G S) :
    Nat.card s.right < Fintype.card V := by
  classical
  obtain ⟨x, _, hx⟩ := s.left_private
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hx

omit [DecidableRel G.Adj] in
/-- A proper separator with disconnected deletion supplies a concrete
separation by one residual reachability class and its complement. -/
theorem exists_separation (S : Finset V) (hsmall : S.card < Fintype.card V)
    (hdis : ¬(G.induce (S : Set V)ᶜ).Connected) : Nonempty (Separation G S) := by
  classical
  have hex : ∃ x : V, x ∉ S := by
    by_contra h
    push Not at h
    have heq : S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    simp [heq] at hsmall
  let H := G.induce (S : Set V)ᶜ
  haveI : Nonempty ↥((S : Set V)ᶜ) := ⟨⟨hex.choose, hex.choose_spec⟩⟩
  have hnot : ¬H.Preconnected := fun h => hdis ⟨h⟩
  change ¬∀ a b, H.Reachable a b at hnot
  push Not at hnot
  obtain ⟨a, b, hab⟩ := hnot
  let R : Set V := {x | ∃ hx : x ∉ S, H.Reachable a ⟨x, hx⟩}
  have haR : a.val ∈ R := ⟨a.property, Reachable.refl a⟩
  have hbR : b.val ∉ R := by
    rintro ⟨hb, hreach⟩
    exact hab hreach
  refine ⟨{
    left := (S : Set V) ∪ R
    right := (S : Set V) ∪ Rᶜ
    cover := ?_
    overlap := ?_
    left_private := ?_
    right_private := ?_
    no_cross := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    tauto
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto
  · refine ⟨a.val, Or.inr haR, ?_⟩
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨a.property, haR⟩
  · refine ⟨b.val, Or.inr hbR, ?_⟩
    simp only [Set.mem_union, not_or]
    exact ⟨b.property, hbR⟩
  · intro x hx y hy hxy
    have hxR : x ∈ R := hx.1.resolve_left (fun hxS => hx.2 (Or.inl hxS))
    have hyS : y ∉ S := fun hyS => hy.2 (Or.inl hyS)
    have hyR : y ∉ R := fun hyR => hy.2 (Or.inr hyR)
    obtain ⟨hxS, hreach⟩ := hxR
    apply hyR
    refine ⟨hyS, hreach.trans ?_⟩
    exact (show H.Adj ⟨x, hxS⟩ ⟨y, hyS⟩ from hxy).reachable

/-- Every non-three-connected graph of order at least four has an actual
proper two-sided separation of order at most two. -/
theorem exists_small_separation (hcard : 4 ≤ Fintype.card V)
    (hnot : ¬G.IsKConnected 3) :
    ∃ S : Finset V, S.card ≤ 2 ∧ Nonempty (Separation G S) := by
  obtain ⟨S, hS, hdis⟩ := not_isKConnected_three_extract G hcard hnot
  exact ⟨S, hS, exists_separation G S (by omega) hdis⟩

/-- Choosing a separator of minimum cardinality also proves the exact
connectivity needed to fill a two-vertex separator side by an outside path. -/
theorem exists_minimum_small_separation (hcard : 4 ≤ Fintype.card V)
    (hnot : ¬G.IsKConnected 3) :
    ∃ S : Finset V, S.card ≤ 2 ∧ G.IsKConnected S.card ∧ Nonempty (Separation G S) := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hex : ∃ k : ℕ, ∃ S : Finset V,
      S.card = k ∧ ¬(G.induce (S : Set V)ᶜ).Connected := by
    obtain ⟨S, _, hdis⟩ := not_isKConnected_three_extract G hcard hnot
    exact ⟨S.card, S, rfl, hdis⟩
  let k := Nat.find hex
  obtain ⟨S, hSk, hdis⟩ := Nat.find_spec hex
  have hk : k ≤ 2 := by
    obtain ⟨T, hT, hdisT⟩ := not_isKConnected_three_extract G hcard hnot
    exact (Nat.find_min' hex ⟨T, rfl, hdisT⟩).trans hT
  have hconn : G.IsVertexConnected k := by
    refine ⟨by omega, ?_⟩
    intro T hT
    have heq : ((Finset.univ \ T : Finset V) : Set V) = (T : Set V)ᶜ := by
      ext w
      simp
    rw [heq]
    by_contra hdisT
    exact Nat.find_min hex hT ⟨T, rfl, hdisT⟩
  refine ⟨S, by omega, ?_, exists_separation G S (by omega) hdis⟩
  rw [hSk]
  exact le_vertexConnectivity_of_isVertexConnected G hconn

#print axioms exists_separation
#print axioms exists_small_separation
#print axioms exists_minimum_small_separation

end PlaneTopology.WagnerSeparation
