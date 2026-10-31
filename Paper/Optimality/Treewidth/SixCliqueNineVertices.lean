import Paper.Optimality.Treewidth.SixCliqueAffineReduction

/-! The small K6 extremal obstruction. A nine-vertex six-regular graph
cannot have four common neighbors on every edge: its two-regular complement
would cover six neighbors by the union of two sets of size two. -/
namespace Paper.SixCliqueNineVertices

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem regular_impossible (hcard : Fintype.card V = 9)
    (hregular : ∀ v, G.degree v = 6)
    (hcn : ∀ u v, G.Adj u v → 4 ≤ Fintype.card (G.commonNeighbors u v)) : False := by
  classical
  have hcomp : ∀ v, Gᶜ.degree v = 2 := by
    intro v
    rw [G.degree_compl, hcard, hregular]
  have hcover : ∀ u v, G.Adj u v → ∃ w, Gᶜ.Adj u w ∧ Gᶜ.Adj v w := by
    intro u v huv
    have hi : (G.neighborFinset u ∩ G.neighborFinset v).card =
        Fintype.card (G.commonNeighbors u v) := by
      simpa only [commonNeighbors, Set.toFinset_inter, ← neighborFinset_def] using
        Set.toFinset_card (G.commonNeighbors u v)
    have hh := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
      hregular, hregular, hi] at hh
    have hc := hcn u v huv
    have hu : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ 8 := by omega
    have hex : ∃ w, w ∉ G.neighborFinset u ∪ G.neighborFinset v := by
      by_contra hn
      push_neg at hn
      have heq := Finset.eq_univ_iff_forall.mpr hn
      rw [heq, Finset.card_univ, hcard] at hu
      omega
    obtain ⟨w, hw⟩ := hex
    have hwu : ¬G.Adj u w := fun h => hw (Finset.mem_union_left _ ((G.mem_neighborFinset u w).mpr h))
    have hwv : ¬G.Adj v w := fun h => hw (Finset.mem_union_right _ ((G.mem_neighborFinset v w).mpr h))
    have huw : u ≠ w := by intro he; subst w; exact hwv huv.symm
    have hvw : v ≠ w := by intro he; subst w; exact hwu huv
    exact ⟨w, (G.compl_adj u w).mpr ⟨huw, hwu⟩,
      (G.compl_adj v w).mpr ⟨hvw, hwv⟩⟩
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let u : V := Classical.arbitrary V
  have htwo : (Gᶜ.neighborFinset u).card = 2 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, hcomp]
  obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp htwo
  have hsubset : G.neighborFinset u ⊆ Gᶜ.neighborFinset a ∪ Gᶜ.neighborFinset b := by
    intro v hv
    obtain ⟨w, huw, hvw⟩ := hcover u v ((G.mem_neighborFinset u v).mp hv)
    have hw : w = a ∨ w = b := by
      have hh : w ∈ Gᶜ.neighborFinset u := (Gᶜ.mem_neighborFinset u w).mpr huw
      simpa only [hab, Finset.mem_insert, Finset.mem_singleton] using hh
    rcases hw with rfl | rfl
    · exact Finset.mem_union_left _ ((Gᶜ.mem_neighborFinset _ _).mpr hvw.symm)
    · exact Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset _ _).mpr hvw.symm)
  have hle := (Finset.card_le_card hsubset).trans
    (Finset.card_union_le (Gᶜ.neighborFinset a) (Gᶜ.neighborFinset b))
  rw [G.card_neighborFinset_eq_degree, Gᶜ.card_neighborFinset_eq_degree,
    Gᶜ.card_neighborFinset_eq_degree, hregular, hcomp, hcomp] at hle
  omega

theorem edge_bound (hG : G.IsKMinorFree 6) (hlo : 4 ≤ Fintype.card V)
    (hhi : Fintype.card V ≤ 9) : G.edgeFinset.card ≤ 4 * Fintype.card V - 10 := by
  classical
  by_contra hn
  obtain ⟨W, _, _, H, _, hm, hH, he, hc, hd, _⟩ :=
    SixCliqueAffineReduction.extract G hG hlo (by omega)
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hW : Fintype.card W ≤ 9 := by
    obtain ⟨model⟩ := hm
    have hh := model.natCard_le
    have hh' : Fintype.card W ≤ Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card] using hh
    omega
  have hmin : 6 ≤ H.minDegree := H.le_minDegree_of_forall_le_degree 6 hd
  have hshake := H.minDegree_mul_card_le_two_mul_card_edges
  have hmul := Nat.mul_le_mul_right (Fintype.card W) hmin
  have hcard : Fintype.card W = 9 := by omega
  have hE : H.edgeFinset.card = 27 := by omega
  have hregular : ∀ v, H.degree v = 6 := by
    intro v
    have hvlow := hd v
    have hsum : (∑ w : W, H.degree w) = 54 := by
      rw [H.sum_degrees_eq_twice_card_edges, hE]
    have hrest : ∑ w ∈ Finset.univ.erase v, 6 ≤
        ∑ w ∈ Finset.univ.erase v, H.degree w := Finset.sum_le_sum (fun w _ => hd w)
    have hvsum := Finset.sum_erase_add (Finset.univ (α := W)) (fun w => H.degree w)
      (Finset.mem_univ v)
    change (∑ w ∈ Finset.univ.erase v, H.degree w) + H.degree v =
      (∑ w : W, H.degree w) at hvsum
    have hsize : (Finset.univ.erase v : Finset W).card = 8 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
    simp only [Finset.sum_const, smul_eq_mul, hsize] at hrest
    omega
  exact regular_impossible H hcard hregular hc

end Paper.SixCliqueNineVertices

#print axioms Paper.SixCliqueNineVertices.regular_impossible
#print axioms Paper.SixCliqueNineVertices.edge_bound
