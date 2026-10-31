import Paper.Optimality.Treewidth.SevenCliqueEightComponent
namespace Paper.CliqueExteriorComplementConnected
open SimpleGraph CliqueComponentBoundary PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem connected (v : V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent) :
    (G.induce (outside G (insert v (G.neighborSet v)) C)ᶜ).Connected := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  have hAX : A ⊆ Xᶜ := by intro z hz hx; exact outside_subset G A C hx hz
  have hvA : v ∈ A := Or.inl rfl
  have hA : (G.induce A).Connected := SevenCliqueEightComponent.closed_connected G v
  apply G.induce_connected_of_patches v (hAX hvA)
  intro y hy
  by_cases hyA : y ∈ A
  · exact ⟨A,hAX,hvA,hyA,hA.preconnected ⟨v,hvA⟩ ⟨y,hyA⟩⟩
  · let D := (G.induce Aᶜ).connectedComponentMk ⟨y,hyA⟩
    let Y := outside G A D
    have hyY : y ∈ Y := ⟨⟨y,hyA⟩,ConnectedComponent.connectedComponentMk_mem,rfl⟩
    have hDC : D ≠ C := by
      intro heq
      apply hy
      change y ∈ outside G A C
      rw [← heq]
      exact hyY
    have hYX : Y ⊆ Xᶜ := by
      rintro z ⟨a,ha,rfl⟩ ⟨b,hb,hba⟩
      have hab : b = a := Subtype.ext hba
      subst b
      exact hDC (((ConnectedComponent.mem_supp_iff D a).mp ha).symm.trans ((ConnectedComponent.mem_supp_iff C a).mp hb))
    have hncl := CliqueNeighborhoodExterior.boundary_not_clique G v Y ⟨y,hyY⟩ (outside_subset G A D) hsep
    have hboundary : (boundary G Y).Nonempty := by
      by_contra hn
      have he : boundary G Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      apply hncl
      simp [he]
    obtain ⟨p,hp⟩ := hboundary
    have hpA := boundary_subset G A D hp
    obtain ⟨_,z,hz,hpz⟩ := (mem_boundary G Y p).mp hp
    have hAY : (G.induce (A ∪ Y)).Connected :=
      SimpleGraph.connected_induce_union hA.preconnected (outside_connected G A D).preconnected hpA hz hpz
    have hsub : A ∪ Y ⊆ Xᶜ := Set.union_subset hAX hYX
    have hvAY : v ∈ A ∪ Y := Or.inl hvA
    have hyAY : y ∈ A ∪ Y := Or.inr hyY
    exact ⟨A ∪ Y,hsub,hvAY,hyAY,hAY.preconnected ⟨v,hvAY⟩ ⟨y,hyAY⟩⟩
theorem contact (hG : G.IsKMinorFree 7) (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ a z, G.Adj a z → 5 ≤ Fintype.card (G.commonNeighbors a z))
    (v : V) (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (SevenCliqueEightExteriorSize.vertices (outside G (insert v (G.neighborSet v)) C)).card ≤ 9)
    (x : V) (hx : x ∈ outside G (insert v (G.neighborSet v)) C) :
    ∃ p, p ∉ outside G (insert v (G.neighborSet v)) C ∧ G.Adj x p := by
  classical
  let X := outside G (insert v (G.neighborSet v)) C
  let T := SevenCliqueEightExteriorSize.vertices X
  have hxT : x ∈ T := (SevenCliqueEightExteriorSize.mem_vertices X x).mpr hx
  by_contra hn
  push Not at hn
  have hsub : G.neighborFinset x ⊆ T.erase x := by
    intro z hz
    have hxz := (G.mem_neighborFinset x z).mp hz
    have hzX : z ∈ X := by by_contra hh; exact hn z hh hxz
    exact Finset.mem_erase.mpr ⟨hxz.ne.symm,(SevenCliqueEightExteriorSize.mem_vertices X z).mpr hzX⟩
  have hh := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree,Finset.card_erase_of_mem hxT] at hh
  have hsz : T.card ≤ 9 := hsize
  have hx8 : G.degree x = 8 := by have hm := hmin x; omega
  have hT9 : T.card = 9 := by omega
  have hclosed : insert x (G.neighborFinset x) = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxT
      · exact Finset.mem_of_mem_erase (hsub hz)
    · rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self x),G.card_neighborFinset_eq_degree,hx8,hT9]
  have hset : insert x (G.neighborSet x) = X := by
    ext z
    rw [← SevenCliqueEightExteriorSize.mem_vertices X z]
    change z ∈ insert x (G.neighborSet x) ↔ z ∈ T
    rw [← hclosed]
    simp only [Set.mem_insert_iff,Finset.mem_insert,G.mem_neighborFinset ]
    rfl
  have hnot := SevenCliqueEightNeighbors.exterior_not_connected G hG x hx8
    (fun z => by rw [hx8]; exact hmin z) (hcn x)
  rw [hset] at hnot
  exact hnot (connected G v hsep C)
theorem free_nine (hG : G.IsKMinorFree 7) (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ a z, G.Adj a z → 5 ≤ Fintype.card (G.commonNeighbors a z))
    (v : V) (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (SevenCliqueEightExteriorSize.vertices (outside G (insert v (G.neighborSet v)) C)).card ≤ 9) :
    (G.induce ((SevenCliqueEightExteriorSize.vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)).IsKMinorFree 6 := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let T := SevenCliqueEightExteriorSize.vertices X
  intro ⟨m⟩
  let n := CliqueInducedLift.model G (T : Set V) m
  have hsub : ∀ i, n.branchSet i ⊆ X := by
    intro i z hz
    exact (SevenCliqueEightExteriorSize.mem_vertices X z).mp (CliqueInducedLift.branch_subset G (T : Set V) m i hz)
  have ha : ∀ i, Disjoint A (n.branchSet i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact outside_subset G A C (hsub i hzB) hzA
  have ht : ∀ i, ∃ a ∈ A, ∃ z ∈ n.branchSet i, G.Adj a z := by
    intro i
    obtain ⟨z,hz⟩ := n.nonempty i
    obtain ⟨a,haX,hza⟩ := contact G hG hmin hcn v hsep C hsize z (hsub i hz)
    exact ⟨a,outside_boundary G A C z (hsub i hz) a haX hza,z,hz,hza.symm⟩
  have hf : (completeGraph (Fin 6)).IsKMinorFree 6 :=
    CliqueConnectedApex.excludes_set 7 (by decide) hG n A ⟨v,by simp [A]⟩
      (SevenCliqueEightComponent.closed_connected G v) ha ht
  exact hf (IsMinor.refl _)
end Paper.CliqueExteriorComplementConnected


