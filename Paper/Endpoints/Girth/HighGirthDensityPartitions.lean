import Mathlib

/-! Exact edge and vertex counts when splitting off a union of components. -/
namespace Paper.HighGirthDensityPartitions
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

set_option backward.isDefEq.respectTransparency false in
theorem induced_card (G : SimpleGraph V) (S : Set V) :
    (G.induce S).edgeFinset.card = (G.edgeFinset ∩ S.toFinset.sym2).card := by
  classical
  have hh := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := G) (s := S))
  simpa only [Finset.card_map] using hh

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem edge_split (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    G.edgeFinset.card = (G.induce S).edgeFinset.card + (G.induce Sᶜ).edgeFinset.card := by
  classical
  let A := G.edgeFinset ∩ S.toFinset.sym2
  let B := G.edgeFinset ∩ Sᶜ.toFinset.sym2
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ u v =>
      have ha : u ∈ S := by simpa [A,Finset.mk_mem_sym2_iff] using (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp he).2).1
      have hb : u ∉ S := by simpa [B,Finset.mk_mem_sym2_iff] using (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hf).2).1
      exact hb ha
  have heq : G.edgeFinset = A ∪ B := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [A,B,Finset.mem_union,Finset.mem_inter,Finset.mk_mem_sym2_iff,
        Set.mem_toFinset,Set.mem_compl_iff,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
      constructor
      · intro he
        by_cases hu : u ∈ S
        · exact Or.inl ⟨he,hu,hclosed u hu v he⟩
        · have hv : v ∉ S := fun hv => hu (hclosed v hv u he.symm)
          exact Or.inr ⟨he,hu,hv⟩
      · rintro (⟨he,_,_⟩ | ⟨he,_,_⟩) <;> exact he
  calc G.edgeFinset.card = (A ∪ B).card := congrArg Finset.card heq
       _ = A.card + B.card := Finset.card_union_of_disjoint hd
       _ = _ := by
         congr 1
         · exact (induced_card G S).symm
         · convert (induced_card G Sᶜ).symm using 1 <;> congr 1 <;> ext e <;> simp [B]

theorem vertex_split (S : Set V) :
    Fintype.card {v // v ∈ S} + Fintype.card {v // v ∉ S} = Fintype.card V := by
  classical
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

end Paper.HighGirthDensityPartitions
#print axioms Paper.HighGirthDensityPartitions.induced_card
#print axioms Paper.HighGirthDensityPartitions.edge_split
#print axioms Paper.HighGirthDensityPartitions.vertex_split
