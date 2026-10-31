import GraphTheory.Plane.WagnerSeparation

/-! An actual outside component and its external boundary. The boundary
itself gives a genuine separation whenever a retained vertex has no edge
into the component. No separator is supplied as a hypothesis. -/
namespace Paper.CliqueComponentBoundary

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} (G : SimpleGraph V)

def outside (A : Set V) (C : (G.induce Aᶜ).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

theorem outside_connected (A : Set V) (C : (G.induce Aᶜ).ConnectedComponent) :
    (G.induce (outside G A C)).Connected := by
  let f : C.toSimpleGraph →g G.induce (outside G A C) :=
    { toFun := fun z => ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
      map_rel' := fun h => h }
  have hf : Function.Surjective f := by
    rintro ⟨z, w, hwC, rfl⟩
    exact ⟨⟨w, hwC⟩, rfl⟩
  exact Connected.map f hf C.connected_toSimpleGraph

theorem outside_subset (A : Set V) (C : (G.induce Aᶜ).ConnectedComponent) :
    outside G A C ⊆ Aᶜ := by
  rintro z ⟨w, _, rfl⟩
  exact w.property

theorem outside_boundary (A : Set V) (C : (G.induce Aᶜ).ConnectedComponent)
    (x : V) (hx : x ∈ outside G A C) (y : V) (hy : y ∉ outside G A C)
    (hadj : G.Adj x y) : y ∈ A := by
  classical
  obtain ⟨w, hwC, rfl⟩ := hx
  by_contra hyA
  exact hy ⟨⟨y, hyA⟩, C.mem_supp_of_adj_mem_supp hwC hadj, rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def boundary (C : Set V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => x ∉ C ∧ ∃ z ∈ C, G.Adj x z)

theorem mem_boundary (C : Set V) (x : V) :
    x ∈ boundary G C ↔ x ∉ C ∧ ∃ z ∈ C, G.Adj x z := by
  classical
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def separation (C : Set V) (hC : C.Nonempty) (v : V)
    (hv : v ∉ C) (hno : ∀ z ∈ C, ¬G.Adj v z) : Separation G (boundary G C) := by
  classical
  let B := boundary G C
  have hBout (x : V) (hx : x ∈ B) : x ∉ C := ((mem_boundary G C x).mp hx).1
  have hvB : v ∉ B := by
    intro hh
    obtain ⟨z, hz, hvz⟩ := ((mem_boundary G C v).mp hh).2
    exact hno z hz hvz
  refine {
    left := C ∪ (B : Set V)
    right := Cᶜ
    cover := ?_
    overlap := ?_
    left_private := ?_
    right_private := ?_
    no_cross := ?_
  }
  · ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    tauto
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff, Finset.mem_coe]
    exact ⟨fun h => h.1.resolve_left h.2, fun h => ⟨Or.inr h, hBout x h⟩⟩
  · obtain ⟨x, hx⟩ := hC
    exact ⟨x, Or.inl hx, fun hh => hh hx⟩
  · exact ⟨v, hv, fun hh => hh.elim hv hvB⟩
  · intro x hx y hy hadj
    have hxC : x ∈ C := by
      by_contra hh
      exact hx.2 hh
    have hyB : y ∉ B := fun hh => hy.2 (Or.inr hh)
    exact hyB ((mem_boundary G C y).mpr ⟨hy.1, x, hxC, hadj.symm⟩)

theorem boundary_subset (A : Set V) (C : (G.induce Aᶜ).ConnectedComponent) :
    (boundary G (outside G A C) : Set V) ⊆ A := by
  intro y hy
  obtain ⟨hyout, x, hx, hyx⟩ := (mem_boundary G _ y).mp hy
  exact outside_boundary G A C x hx y hyout hyx.symm

end Paper.CliqueComponentBoundary

#print axioms Paper.CliqueComponentBoundary.outside_connected
#print axioms Paper.CliqueComponentBoundary.outside_subset
#print axioms Paper.CliqueComponentBoundary.outside_boundary
#print axioms Paper.CliqueComponentBoundary.separation
#print axioms Paper.CliqueComponentBoundary.boundary_subset
