import Paper.Optimality.Treewidth.CliqueExteriorSmallDeletion
import Paper.Optimality.Treewidth.CliqueLargeComponentsConnected
namespace Paper.CliqueExteriorFiveImpossible
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 7) (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ a z, G.Adj a z → 5 ≤ Fintype.card (G.commonNeighbors a z))
    (he : G.edgeFinset.card+14 = 5*Fintype.card V)
    (hminimal : CliqueMinorMinimal.BelowThreshold G 5 14 5) (v : V)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card ≤ 9)
    (x : V) (hx : x ∈ outside G (insert v (G.neighborSet v)) C)
    (hx8 : G.degree x = 8)
    (h5 : G.inducedDegree x (vertices (outside G (insert v (G.neighborSet v)) C)) = 5) : False := by
  classical
  let A := insert v (G.neighborSet v)
  let X := outside G A C
  let T := vertices X
  have hxT : x ∈ T := (mem_vertices X x).mpr hx
  have hsz : T.card ≤ 9 := hsize
  change G.inducedDegree x T = 5 at h5
  let S := G.neighborFinset x \ T
  have hSf : S = Tᶜ.filter (G.Adj x) := by
    ext z
    simp only [S,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_compl,G.mem_neighborFinset]
    tauto
  have hS3 : S.card = 3 := by
    have hp := CliquePartitionDegrees.partition G T x
    rw [hx8,h5] at hp
    rw [hSf]
    change G.inducedDegree x Tᶜ = 3
    omega
  have hSn : S ⊆ G.neighborFinset v := by
    intro z hz
    obtain ⟨hzN,hzT⟩ := Finset.mem_sdiff.mp hz
    have hxz := (G.mem_neighborFinset x z).mp hzN
    have hzX : z ∉ X := fun hh => hzT ((mem_vertices X z).mpr hh)
    have hzA := outside_boundary G A C x hx z hzX hxz
    rcases hzA with rfl | hzA
    · exact False.elim (outside_subset G A C hx (Or.inr hxz.symm))
    · exact (G.mem_neighborFinset v z).mpr hzA
  have hbd : ∀ D : (G.induce Aᶜ).ConnectedComponent, 4 ≤ (boundary G (outside G A D)).card := by
    intro D
    obtain ⟨z,hz⟩ := D.nonempty_supp
    have hne : (outside G A D).Nonempty := ⟨z.val,z,hz,rfl⟩
    exact (CliqueAffineBoundaryBudget.boundary_budget G he
      (fun z => by have hh := hmin z; omega) hminimal v _ hne (outside_subset G A D)).2
  let R := (X ∪ (S : Set V))ᶜ
  have hR : (G.induce R).Connected := CliqueExteriorSmallDeletion.connected G v hbd C S hSn (by omega)
  let U := (insert x (G.neighborSet x))ᶜ
  have hRU : R ⊆ U := by
    intro z hz hclosed
    have hzX : z ∉ X := fun hh => hz (Or.inl hh)
    have hzT : z ∉ T := fun hh => hzX ((mem_vertices X z).mp hh)
    rcases hclosed with rfl | hxz
    · exact hzX hx
    · have hzS : z ∈ S := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x z).mpr hxz,hzT⟩
      exact hz (Or.inr hzS)
  let P := T \ insert x (G.neighborFinset x)
  have hwitness : (T.filter (G.Adj x)).Nonempty := Finset.card_pos.mp (by change 0 < G.inducedDegree x T; omega)
  obtain ⟨w,hw⟩ := hwitness
  obtain ⟨hwT,hxw⟩ := Finset.mem_filter.mp hw
  have hPsub : P ⊆ (T.erase x).erase w := by
    intro z hz
    obtain ⟨hzT,hzN⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun hh => hzN (Finset.mem_insert.mpr (Or.inl hh))
    have hzw : z ≠ w := by
      intro hzw
      subst z
      exact hzN (Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset x w).mpr hxw)))
    exact Finset.mem_erase.mpr ⟨hzw,Finset.mem_erase.mpr ⟨hzx,hzT⟩⟩
  have hwErase : w ∈ T.erase x := Finset.mem_erase.mpr ⟨hxw.ne.symm,hwT⟩
  have hP : P.card ≤ 7 := by
    have hh := Finset.card_le_card hPsub
    rw [Finset.card_erase_of_mem hwErase,Finset.card_erase_of_mem hxT] at hh
    omega
  have hcover : U ⊆ R ∪ (P : Set V) := by
    intro z hz
    by_cases hzT : z ∈ T
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨hzT,?_⟩
      intro hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hz (Or.inl rfl)
      · exact hz (Or.inr ((G.mem_neighborFinset x z).mp hc))
    · left
      intro hc
      rcases hc with hzX | hzS
      · exact hzT ((mem_vertices X z).mpr hzX)
      · have hh := (Finset.mem_sdiff.mp hzS).1
        exact hz (Or.inr ((G.mem_neighborFinset x z).mp hh))
  have hlarge : ∀ D : (G.induce U).ConnectedComponent,
      8 ≤ (vertices (Subtype.val '' D.supp)).card := by
    intro D
    exact SevenCliqueEightComponent.component_eight G hG x hx8
      (fun z => by rw [hx8]; exact hmin z) (hcn x) D
  have hconn : (G.induce U).Connected := CliqueLargeComponentsConnected.connected G U R hR hRU P hP hcover hlarge
  exact SevenCliqueEightNeighbors.exterior_not_connected G hG x hx8
    (fun z => by rw [hx8]; exact hmin z) (hcn x) hconn
end Paper.CliqueExteriorFiveImpossible
