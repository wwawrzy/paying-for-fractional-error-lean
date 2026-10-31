import Paper.Optimality.Treewidth.CliqueStarProjection
import Paper.Optimality.Treewidth.CliqueRootedProjection

/-! Exact control of an outside-branch projection in a K6-free graph.
An actual missing attachment edge strictly increases the induced edge
count, while the retained apex forces the K5 extremal bound. -/
namespace Paper.CliqueStarBound

open SimpleGraph CliqueStarProjection
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem growth (A : Set V) [Fintype A] (u w : A) (S : Set V)
    (hne : u ≠ w) (hnot : ¬G.Adj u.val w.val)
    (hattach : ∃ z ∈ S, G.Adj z w.val) :
    (G.induce A).edgeFinset.card < (fill G A u S).edgeFinset.card := by
  classical
  have hle : G.induce A ≤ fill G A u S := fun _ _ h => Or.inl h
  have hnew : (fill G A u S).Adj u w := Or.inr ⟨hne, Or.inl ⟨rfl, hattach⟩⟩
  have hlt : G.induce A < fill G A u S := lt_of_le_not_ge hle (fun hh => hnot (hh hnew))
  exact Finset.card_lt_card (edgeFinset_strict_mono hlt)

theorem growth_two (A : Set V) [Fintype A] (u w₁ w₂ : A) (S : Set V)
    (hne₁ : u ≠ w₁) (hne₂ : u ≠ w₂) (hww : w₁ ≠ w₂)
    (hnot₁ : ¬G.Adj u.val w₁.val) (hnot₂ : ¬G.Adj u.val w₂.val)
    (hattach₁ : ∃ z ∈ S, G.Adj z w₁.val)
    (hattach₂ : ∃ z ∈ S, G.Adj z w₂.val) :
    (G.induce A).edgeFinset.card + 2 ≤ (fill G A u S).edgeFinset.card := by
  classical
  let e₁ : Sym2 A := s(u, w₁)
  let e₂ : Sym2 A := s(u, w₂)
  have hold : G.induce A ≤ fill G A u S := fun _ _ h => Or.inl h
  have hn₁ : e₁ ∉ (G.induce A).edgeFinset := by
    simpa only [e₁, mem_edgeFinset, mem_edgeSet] using hnot₁
  have hn₂ : e₂ ∉ (G.induce A).edgeFinset := by
    simpa only [e₂, mem_edgeFinset, mem_edgeSet] using hnot₂
  have hnew₁ : e₁ ∈ (fill G A u S).edgeFinset := by
    apply mem_edgeFinset.mpr
    exact Or.inr ⟨hne₁, Or.inl ⟨rfl, hattach₁⟩⟩
  have hnew₂ : e₂ ∈ (fill G A u S).edgeFinset := by
    apply mem_edgeFinset.mpr
    exact Or.inr ⟨hne₂, Or.inl ⟨rfl, hattach₂⟩⟩
  have hne : e₁ ≠ e₂ := by
    intro hh
    rcases Sym2.eq_iff.mp hh with ⟨_, hw⟩ | ⟨hu, _⟩
    · exact hww hw
    · exact hne₂ hu
  have hsub : insert e₁ (insert e₂ (G.induce A).edgeFinset) ⊆
      (fill G A u S).edgeFinset := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hnew₁
    · rcases Finset.mem_insert.mp he with rfl | he
      · exact hnew₂
      · exact (edgeFinset_mono hold) he
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, not_or]; exact ⟨hne, hn₁⟩),
    Finset.card_insert_of_notMem hn₂] at hh
  omega

theorem edge_bound (hG : G.IsKMinorFree 6) (v : V)
    (A : Set V) [Fintype A] (hA : A ⊆ G.neighborSet v)
    (u : A) (S : Set V) (huS : u.val ∈ S) (hS : (G.induce S).Connected)
    (hside : ∀ z ∈ S, z ∈ A → z = u.val) (hvS : v ∉ S)
    (hsize : 3 ≤ Fintype.card A) :
    (fill G A u S).edgeFinset.card ≤ 3 * Fintype.card A - 6 := by
  classical
  let m := model G A u S huS hS hside
  have hvA : v ∉ A := fun hh => G.loopless.irrefl v (hA hh)
  have hself (a : A) : a.val ∈ m.branchSet a := by
    dsimp only [m, CliqueStarProjection.model]
    split
    · rename_i ha
      subst a
      exact huS
    · rfl
  have havoid (a : A) : v ∉ m.branchSet a := by
    dsimp only [m, CliqueStarProjection.model]
    split
    · exact hvS
    · intro hh
      exact hvA ((show v = a.val from hh).symm ▸ a.property)
  exact CliqueRootedProjection.edge_bound hG m v havoid
    (fun a => ⟨a.val, hself a, hA a.property⟩) hsize

end Paper.CliqueStarBound

#print axioms Paper.CliqueStarBound.growth
#print axioms Paper.CliqueStarBound.growth_two
#print axioms Paper.CliqueStarBound.edge_bound
