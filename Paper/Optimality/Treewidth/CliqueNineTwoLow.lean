import Paper.Optimality.Treewidth.CliqueEightExtremalClassification
namespace Paper.CliqueNineTwoLow
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
theorem two_low (hf : H.IsKMinorFree 6) (hV : Fintype.card V = 9)
    (he : H.edgeFinset.card = 26) :
    2 ≤ (Finset.univ.filter (fun x => H.degree x ≤ 5)).card := by
  classical
  let L := Finset.univ.filter (fun x => H.degree x ≤ 5)
  have hmin : ∀ x, 4 ≤ H.degree x := by
    intro x
    exact CliqueSixExtremalGeneral.four_le H hf (by omega) (by rw [he,hV]) x
  have hs := H.sum_degrees_eq_twice_card_edges
  rw [he] at hs
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := H.exists_minimal_degree_vertex
  have hmul := H.minDegree_mul_card_le_two_mul_card_edges
  rw [he,hV] at hmul
  have hu5 : H.degree u ≤ 5 := by omega
  have huL : u ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu5⟩
  by_contra hn
  change ¬2 ≤ L.card at hn
  have hL : L = {u} := by
    symm
    exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr huL) (by simp; omega)
  have hother : ∀ x, x ≠ u → 6 ≤ H.degree x := by
    intro x hxu
    by_contra hx
    have hxL : x ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [hL,Finset.mem_singleton] at hxL
    exact hxu hxL
  have hrest : 48 ≤ ∑ x ∈ Finset.univ.erase u, H.degree x := by
    calc
      48 = ∑ _x ∈ (Finset.univ.erase u : Finset V), (6 : ℕ) := by simp [hV]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hother x (Finset.mem_erase.mp hx).1)
  have heq := Finset.sum_erase_add (Finset.univ : Finset V) (fun x => H.degree x) (Finset.mem_univ u)
  change (∑ x ∈ Finset.univ.erase u, H.degree x)+H.degree u = ∑ x, H.degree x at heq
  have hu4 : H.degree u = 4 := by have hh := hmin u; omega
  have hall6 : ∀ x, x ≠ u → H.degree x = 6 := by
    intro x hxu
    have h64 := hother x hxu
    have hxmem : x ∈ (Finset.univ.erase u : Finset V) := by simp [hxu]
    have hsmall : 42 ≤ ∑ y ∈ (Finset.univ.erase u).erase x, H.degree y := by
      calc
        42 = ∑ _y ∈ ((Finset.univ.erase u).erase x : Finset V), (6 : ℕ) := by
          rw [Finset.sum_const,Finset.card_erase_of_mem hxmem]
          simp [hV]
        _ ≤ _ := Finset.sum_le_sum (fun y hy => hother y (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1)
    have hxsum := Finset.sum_erase_add (Finset.univ.erase u) (fun y => H.degree y) hxmem
    change (∑ y ∈ (Finset.univ.erase u).erase x, H.degree y)+H.degree x = ∑ y ∈ Finset.univ.erase u, H.degree y at hxsum
    omega
  let T : Set V := {u}ᶜ
  let J := H.induce T
  have hJcard : Fintype.card T = 8 := by simp [T,Fintype.card_compl_set,hV]
  have hJfree : J.IsKMinorFree 6 := IsHMinorFree.minor hf (IsMinor.of_induce H T)
  have hJedges : J.edgeFinset.card = 22 := by
    have hh := (H.card_edgeFinset_induce_compl_singleton u).trans (H.card_edgeFinset_deleteIncidenceSet u)
    change J.edgeFinset.card = H.edgeFinset.card-H.degree u at hh
    omega
  have hbounds : ∀ x : T, J.degree x ≤ H.degree x.val ∧ H.degree x.val ≤ J.degree x+1 := by
    intro x
    let R : Finset V := Finset.univ.erase u
    have hRT : (R : Set V) = T := by ext z; simp [R,T]
    have hxR : x.val ∈ R := by change x.val ∈ (R : Set V); rw [hRT]; exact x.property
    have hdx : J.degree x = H.inducedDegree x.val R := by
      let er : (R : Set V) ≃ T := Equiv.setCongr hRT
      let iso : (H.induce (R : Set V)) ≃g J := { toEquiv := er, map_rel_iff' := by intro a b; rfl }
      have hi := iso.degree_eq ⟨x.val,hxR⟩
      have heq : iso ⟨x.val,hxR⟩ = x := by apply Subtype.ext; rfl
      rw [heq] at hi
      exact hi.trans (InducedCounting.degree_induce_eq_inducedDegree H R ⟨x.val,hxR⟩)
    have hRc : Rᶜ = {u} := by ext z; simp [R]
    have hp := CliquePartitionDegrees.partition H R x.val
    have hone : H.inducedDegree x.val Rᶜ ≤ 1 := by
      rw [hRc]
      exact (H.inducedDegree_le_card x.val {u}).trans (by simp)
    omega
  have hJdeg : ∀ x : T, 5 ≤ J.degree x := by
    intro x
    have hx6 := hall6 x.val x.property
    have hxdel := hbounds x
    omega
  obtain ⟨e⟩ := CliqueEightExtremalClassification.canonical J hJfree hJcard hJedges hJdeg
  let x := e.symm 7
  have hx7 := e.degree_eq x
  have he7 : (CliqueEightResidualTemplates.graph 0 1).degree 7 = 7 := by decide
  have hex : e x = 7 := e.apply_symm_apply 7
  rw [hex,he7] at hx7
  have hx6 := hall6 x.val x.property
  have hdle := J.degree_le_card_edgeFinset (v := x)
  have hcomp := hbounds x
  omega
theorem two_low_near (hf : H.IsKMinorFree 6) (hV : Fintype.card V = 9)
    (he : H.edgeFinset.card = 25) :
    2 ≤ (Finset.univ.filter (fun x => H.degree x ≤ 5)).card := by
  classical
  let L := Finset.univ.filter (fun x => H.degree x ≤ 5)
  have hmin : ∀ x, 3 ≤ H.degree x := by
    intro x
    exact show 3 ≤ H.degree x from by
      have hh := CliqueSixExtremalGeneral.degree_deficit H hf (by omega) 11 (by rw [he,hV]) x
      omega
  have hs := H.sum_degrees_eq_twice_card_edges
  rw [he] at hs
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := H.exists_minimal_degree_vertex
  have hmul := H.minDegree_mul_card_le_two_mul_card_edges
  rw [he,hV] at hmul
  have hu5 : H.degree u ≤ 5 := by omega
  have huL : u ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu5⟩
  by_contra hn
  change ¬2 ≤ L.card at hn
  have hL : L = {u} := by
    symm
    exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr huL) (by simp; omega)
  have hother : ∀ x, x ≠ u → 6 ≤ H.degree x := by
    intro x hxu
    by_contra hx
    have hxL : x ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [hL,Finset.mem_singleton] at hxL
    exact hxu hxL
  have hrest : 48 ≤ ∑ x ∈ Finset.univ.erase u, H.degree x := by
    calc
      48 = ∑ _x ∈ (Finset.univ.erase u : Finset V), (6 : ℕ) := by simp [hV]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hother x (Finset.mem_erase.mp hx).1)
  have heq := Finset.sum_erase_add (Finset.univ : Finset V) (fun x => H.degree x) (Finset.mem_univ u)
  change (∑ x ∈ Finset.univ.erase u, H.degree x)+H.degree u = ∑ x, H.degree x at heq
  have hl := hmin u
  omega
end Paper.CliqueNineTwoLow
