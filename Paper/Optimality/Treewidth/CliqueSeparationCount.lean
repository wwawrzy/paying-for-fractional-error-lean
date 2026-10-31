import GraphTheory.Plane.WagnerSeparation

/-! Exact edge and vertex accounting across an actual separation. Edges in
the separator are counted twice, and no edge crosses the private sides. -/
namespace Paper.CliqueSeparationCount

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edges (A : Set V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset ∩ A.toFinset.sym2

theorem card_edges (A : Set V) [Fintype A] :
    (edges G A).card = (G.induce A).edgeFinset.card := by
  classical
  have hmap : (G.induce A).edgeFinset.map (Function.Embedding.subtype (· ∈ A)).sym2Map =
      edges G A := by
    dsimp only [edges]
    aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])
  have hh := congrArg Finset.card hmap
  simpa only [Finset.card_map] using hh.symm

theorem union {S : Finset V} (s : Separation G S) :
    edges G s.left ∪ edges G s.right = G.edgeFinset := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [edges, Finset.mem_union, Finset.mem_inter, Finset.mk_mem_sym2_iff,
      Set.mem_toFinset, mem_edgeFinset, mem_edgeSet]
    constructor
    · intro h
      exact h.elim And.left And.left
    · intro hxy
      have hx : x ∈ s.left ∨ x ∈ s.right := by
        have hh : x ∈ s.left ∪ s.right := by rw [s.cover]; trivial
        exact hh
      have hy : y ∈ s.left ∨ y ∈ s.right := by
        have hh : y ∈ s.left ∪ s.right := by rw [s.cover]; trivial
        exact hh
      by_cases hxR : x ∈ s.right
      · by_cases hyR : y ∈ s.right
        · exact Or.inr ⟨hxy, hxR, hyR⟩
        · have hyL := hy.resolve_right hyR
          by_cases hxL : x ∈ s.left
          · exact Or.inl ⟨hxy, hxL, hyL⟩
          · exact False.elim (s.no_cross y ⟨hyL, hyR⟩ x ⟨hxR, hxL⟩ hxy.symm)
      · have hxL := hx.resolve_right hxR
        by_cases hyL : y ∈ s.left
        · exact Or.inl ⟨hxy, hxL, hyL⟩
        · exact False.elim (s.no_cross x ⟨hxL, hxR⟩ y ⟨hy.resolve_left hyL, hyL⟩ hxy)

theorem inter {S : Finset V} (s : Separation G S) :
    edges G s.left ∩ edges G s.right = edges G (S : Set V) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    have hS (z : V) : z ∈ S ↔ z ∈ s.left ∧ z ∈ s.right := by
      change z ∈ (S : Set V) ↔ _
      rw [← s.overlap]
      rfl
    simp only [edges, Finset.mem_inter, Finset.mk_mem_sym2_iff,
      Set.mem_toFinset, Finset.mem_coe, hS]
    tauto

theorem edge_sum {S : Finset V} (s : Separation G S)
    [Fintype s.left] [Fintype s.right] [Fintype (S : Set V)] :
    (G.induce s.left).edgeFinset.card + (G.induce s.right).edgeFinset.card =
      G.edgeFinset.card + (G.induce (S : Set V)).edgeFinset.card := by
  classical
  have hh := Finset.card_union_add_card_inter (edges G s.left) (edges G s.right)
  rw [union G s, inter G s, card_edges, card_edges, card_edges] at hh
  exact hh.symm

theorem vertex_sum {S : Finset V} (s : Separation G S)
    [Fintype s.left] [Fintype s.right] :
    Fintype.card s.left + Fintype.card s.right = Fintype.card V + S.card := by
  classical
  have hu : s.left.toFinset ∪ s.right.toFinset = Finset.univ := by
    ext x
    simpa only [Finset.mem_union, Set.mem_toFinset, Finset.mem_univ, iff_true] using
      (show x ∈ s.left ∪ s.right by rw [s.cover]; trivial)
  have hi : s.left.toFinset ∩ s.right.toFinset = S := by
    ext x
    simp only [Finset.mem_inter, Set.mem_toFinset]
    change x ∈ s.left ∩ s.right ↔ x ∈ (S : Set V)
    rw [s.overlap]
  have hh := Finset.card_union_add_card_inter s.left.toFinset s.right.toFinset
  rw [hu, hi, Finset.card_univ, Set.toFinset_card, Set.toFinset_card] at hh
  exact hh.symm

end Paper.CliqueSeparationCount

#print axioms Paper.CliqueSeparationCount.edge_sum
#print axioms Paper.CliqueSeparationCount.vertex_sum
