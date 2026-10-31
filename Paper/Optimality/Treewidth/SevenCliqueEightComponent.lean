import Paper.Optimality.Treewidth.SevenCliqueSevenDense
import Paper.Optimality.Treewidth.SevenCliqueSevenComponent
import Paper.Optimality.Treewidth.CliqueInducedLift
namespace Paper.SevenCliqueEightComponent
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem closed_connected (v : V) : (G.induce (insert v (G.neighborSet v))).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨v,by simp⟩,?_⟩
  intro w
  rcases w.property with he | ha
  · have hh : w = ⟨v,by simp⟩ := Subtype.ext he
    rw [hh]
  · exact (show (G.induce (insert v (G.neighborSet v))).Adj ⟨v,by simp⟩ w from ha).reachable

theorem component_eight (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    8 ≤ (vertices (outside G (insert v (G.neighborSet v)) C)).card := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let T := vertices X
  have hseven := SevenCliqueSevenComponent.component_seven G hG v hv8 hmin hcn C
  change 7 ≤ T.card at hseven
  change 8 ≤ T.card
  by_contra hn
  have hsize : T.card = 7 := by omega
  obtain ⟨_,_,⟨m⟩⟩ := SevenCliqueSevenDense.component_model G hG v hv8 hmin hcn C hsize
  let n := CliqueInducedLift.model G (T : Set V) m
  have hsub : ∀ i, n.branchSet i ⊆ X := by
    intro i z hz
    exact (mem_vertices X z).mp (CliqueInducedLift.branch_subset G (T : Set V) m i hz)
  have hout := outside_subset G A C
  have ha : ∀ i, Disjoint A (n.branchSet i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact hout (hsub i hzB) hzA
  have ht : ∀ i, ∃ a ∈ A, ∃ z ∈ n.branchSet i, G.Adj a z := by
    intro i
    obtain ⟨z,hz⟩ := n.nonempty i
    have hzX := hsub i hz
    have hd : 8 ≤ G.degree z := by have hh := hmin z; omega
    obtain ⟨a,haN,haT⟩ : ∃ a ∈ G.neighborFinset z, a ∉ T := by
      by_contra hn
      push Not at hn
      have hh := Finset.card_le_card (show G.neighborFinset z ⊆ T from hn)
      rw [G.card_neighborFinset_eq_degree] at hh
      omega
    have hza := (G.mem_neighborFinset z a).mp haN
    have haX : a ∉ X := fun hh => haT ((mem_vertices X a).mpr hh)
    exact ⟨a,outside_boundary G A C z hzX a haX hza,z,hz,hza.symm⟩
  have hf : (completeGraph (Fin 6)).IsKMinorFree 6 :=
    CliqueConnectedApex.excludes_set 7 (by decide) hG n A ⟨v,by simp [A]⟩
      (closed_connected G v) ha ht
  exact hf (IsMinor.refl _)
theorem order_twenty_five (hG : G.IsKMinorFree 7) (v : V) (hv : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (hproper : G.degree v+1 < Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S)) :
    25 ≤ Fintype.card V := by
  classical
  obtain ⟨C,D,hCD,hdis,hno,hclC,hclD⟩ := SevenCliqueEightComponents.separated_pair G hG v hv hmin hcn hproper hsep
  let A := insert v (G.neighborFinset v)
  let X := vertices (outside G (insert v (G.neighborSet v)) C)
  let Y := vertices (outside G (insert v (G.neighborSet v)) D)
  have hX : 8 ≤ X.card := component_eight G hG v hv hmin hcn C
  have hY : 8 ≤ Y.card := component_eight G hG v hv hmin hcn D
  have hA : A.card = 9 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),G.card_neighborFinset_eq_degree,hv]
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzY
    exact Set.disjoint_left.mp hdis ((mem_vertices _ z).mp hzX) ((mem_vertices _ z).mp hzY)
  have hAXY : Disjoint A (X ∪ Y) := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzXY
    have hzClosed : z ∈ insert v (G.neighborSet v) := by
      simpa only [A,Finset.mem_insert,G.mem_neighborFinset,Set.mem_insert_iff,Set.mem_setOf_eq] using hzA
    rcases Finset.mem_union.mp hzXY with hzX | hzY
    · exact outside_subset G (insert v (G.neighborSet v)) C ((mem_vertices _ z).mp hzX) hzClosed
    · exact outside_subset G (insert v (G.neighborSet v)) D ((mem_vertices _ z).mp hzY) hzClosed
  have hh := Finset.card_le_card (Finset.subset_univ (A ∪ (X ∪ Y)))
  rw [Finset.card_union_of_disjoint hAXY,Finset.card_union_of_disjoint hXY,hA,Finset.card_univ] at hh
  omega

/-- Any exterior component of order at most eight is K6-minor-free. -/
theorem small_component_free (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsmall : (vertices (outside G (insert v (G.neighborSet v)) C)).card ≤ 8) :
    (G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)).IsKMinorFree 6 := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let T := vertices X
  change T.card ≤ 8 at hsmall
  intro ⟨m⟩
  let n := CliqueInducedLift.model G (T : Set V) m
  have hsub : ∀ i, n.branchSet i ⊆ X := by
    intro i z hz
    exact (mem_vertices X z).mp (CliqueInducedLift.branch_subset G (T : Set V) m i hz)
  have hout := outside_subset G A C
  have ha : ∀ i, Disjoint A (n.branchSet i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact hout (hsub i hzB) hzA
  have ht : ∀ i, ∃ a ∈ A, ∃ z ∈ n.branchSet i, G.Adj a z := by
    intro i
    obtain ⟨z,hz⟩ := n.nonempty i
    have hzX := hsub i hz
    have hd : 8 ≤ G.degree z := by have hh := hmin z; omega
    obtain ⟨a,haN,haT⟩ : ∃ a ∈ G.neighborFinset z, a ∉ T := by
      by_contra hn
      push Not at hn
      have hs : G.neighborFinset z ⊆ T.erase z := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset z a).mp ha).ne.symm,hn a ha⟩
      have hh := Finset.card_le_card hs
      rw [G.card_neighborFinset_eq_degree,Finset.card_erase_of_mem ((mem_vertices X z).mpr hzX)] at hh
      change G.degree z ≤ T.card-1 at hh
      omega
    have hza := (G.mem_neighborFinset z a).mp haN
    have haX : a ∉ X := fun hh => haT ((mem_vertices X a).mpr hh)
    exact ⟨a,outside_boundary G A C z hzX a haX hza,z,hz,hza.symm⟩
  have hf : (completeGraph (Fin 6)).IsKMinorFree 6 :=
    CliqueConnectedApex.excludes_set 7 (by decide) hG n A ⟨v,by simp [A]⟩
      (closed_connected G v) ha ht
  exact hf (IsMinor.refl _)
end Paper.SevenCliqueEightComponent


