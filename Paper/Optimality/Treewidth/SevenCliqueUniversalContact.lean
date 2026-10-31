import Paper.Optimality.Treewidth.SevenCliqueTwentySixClassification
namespace Paper.SevenCliqueTwentySixClassification
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem template_universal (a b : Fin 5)
    (hp : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) :
    (CliqueEightResidualTemplates.graph a b).degree 7 = 7 := by
  rcases hp with h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;> decide

theorem universal_contact (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    let T := vertices (outside G (insert v (G.neighborSet v)) C)
    ∃ x ∈ T, G.inducedDegree x T = 7 ∧ G.inducedDegree x Tᶜ = 1 := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  obtain ⟨a,b,⟨e⟩,hp⟩ := component G hG horder hmin hcn hsep v hv8 C hsize
  let x : (T : Set V) := e.symm 7
  have hi := e.degree_eq x
  have hx : e x = 7 := e.apply_symm_apply 7
  rw [hx,template_universal a b hp] at hi
  have hinner : G.inducedDegree x.val T = 7 := by
    rw [← InducedCounting.degree_induce_eq_inducedDegree G T x]
    exact hi.symm
  have h8 := SevenCliqueEightRegular.component_regular G hG v hv8
    (fun z => by rw [hv8]; exact hmin z) (hcn v) C hsize x.val x.property
  have hpart := CliquePartitionDegrees.partition G T x.val
  change ∃ x ∈ T, G.inducedDegree x T = 7 ∧ G.inducedDegree x Tᶜ = 1
  exact ⟨x.val,x.property,hinner,by omega⟩
theorem unique_outside (T : Finset V) (x : V)
    (hd : G.inducedDegree x Tᶜ = 1) :
    ∃ p ∉ T, G.Adj x p ∧ ∀ y, y ∉ T → G.Adj x y → y = p := by
  classical
  change (Tᶜ.filter (G.Adj x)).card = 1 at hd
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hd
  have hm : p ∈ Tᶜ.filter (G.Adj x) := by rw [hp]; simp
  obtain ⟨hpo,hxp⟩ := Finset.mem_filter.mp hm
  refine ⟨p,Finset.mem_compl.mp hpo,hxp,?_⟩
  intro y hy hxy
  have hm : y ∈ Tᶜ.filter (G.Adj x) := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hy,hxy⟩
  rw [hp,Finset.mem_singleton] at hm
  exact hm
end Paper.SevenCliqueTwentySixClassification
