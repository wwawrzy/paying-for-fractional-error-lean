import GraphTheory.Plane.WagnerSeparatorPaths

/-!
# Filled sides from a genuine two-vertex separation

The outside component is extracted from the actual separation data. No
component, path, minor, or embedding is postulated in the final theorem.
-/

namespace PlaneTopology.WagnerSeparatorSides

open SimpleGraph PlaneTopology.WagnerSeparatorPaths

variable {V : Type*} (G : SimpleGraph V)

/-- A residual edge cannot enter the left side from its complement:
doing so would cross between the two private sides of the separation. -/
theorem residual_adj_outside_left (L R : Set V) (u v : V)
    (hcover : L ∪ R = Set.univ) (hinter : L ∩ R = {u, v})
    (hcross : ∀ a ∈ L \ R, ∀ b ∈ R \ L, ¬G.Adj a b)
    (a b : {w : V // w ≠ u ∧ w ≠ v})
    (ha : a.val ∉ L) (hadj : G.Adj a.val b.val) : b.val ∉ L := by
  intro hbL
  have haR : a.val ∈ R := by
    have h : a.val ∈ L ∪ R := by rw [hcover]; trivial
    exact h.resolve_left ha
  have hbR : b.val ∉ R := by
    intro hbR
    have hb : b.val ∈ ({u, v} : Set V) := hinter ▸ (show b.val ∈ L ∩ R from ⟨hbL, hbR⟩)
    rcases hb with hbu | hbv
    · exact b.property.1 hbu
    · exact b.property.2 hbv
  exact hcross b.val ⟨hbL, hbR⟩ a.val ⟨haR, ha⟩ hadj.symm

/-- Every actual residual walk starting outside the left side remains outside. -/
theorem residual_walk_outside_left (L R : Set V) (u v : V)
    (hcover : L ∪ R = Set.univ) (hinter : L ∩ R = {u, v})
    (hcross : ∀ a ∈ L \ R, ∀ b ∈ R \ L, ¬G.Adj a b)
    {a b : {w : V // w ≠ u ∧ w ≠ v}}
    (p : (G.induce {w | w ≠ u ∧ w ≠ v}).Walk a b) :
    a.val ∉ L → b.val ∉ L := by
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
    intro ha
    exact ih (residual_adj_outside_left G L R u v hcover hinter hcross a b ha hab)

/-- The private right side contains a real component of G-{u,v}, and the
whole component lies outside the left side. -/
theorem exists_outside_component_of_separation (L R : Set V) (u v : V)
    (hcover : L ∪ R = Set.univ) (hinter : L ∩ R = {u, v})
    (hcross : ∀ a ∈ L \ R, ∀ b ∈ R \ L, ¬G.Adj a b)
    (hR : (R \ L).Nonempty) :
    ∃ C : (G.induce {w | w ≠ u ∧ w ≠ v}).ConnectedComponent,
      separatorComponentSet G u v C ⊆ Lᶜ := by
  have huL : u ∈ L := by
    have h : u ∈ L ∩ R := by rw [hinter]; simp
    exact h.1
  have hvL : v ∈ L := by
    have h : v ∈ L ∩ R := by rw [hinter]; simp
    exact h.1
  obtain ⟨w, _, hwL⟩ := hR
  have hwu : w ≠ u := fun h => hwL (h.symm ▸ huL)
  have hwv : w ≠ v := fun h => hwL (h.symm ▸ hvL)
  let root : {z : V // z ≠ u ∧ z ≠ v} := ⟨w, hwu, hwv⟩
  let C := (G.induce {z | z ≠ u ∧ z ≠ v}).connectedComponentMk root
  refine ⟨C, ?_⟩
  rintro z ⟨x, hxC, rfl⟩
  have hroot : root ∈ C.supp := rfl
  obtain ⟨p⟩ := C.reachable_of_mem_supp hroot hxC
  exact residual_walk_outside_left G L R u v hcover hinter hcross p hwL

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A genuinely separated left side, filled along the two separator
vertices, is planar. All outside component/path/minor witnesses are derived. -/
theorem filledLeft_isPlanar (hG : G.IsPlanar) (h2 : G.IsKConnected 2)
    (L R : Set V) (u v : L) (hne : u ≠ v)
    (hcover : L ∪ R = Set.univ) (hinter : L ∩ R = {u.val, v.val})
    (hcross : ∀ a ∈ L \ R, ∀ b ∈ R \ L, ¬G.Adj a b)
    (hR : (R \ L).Nonempty) :
    ((G.induce L) ⊔ edge u v).IsPlanar := by
  obtain ⟨C, hC⟩ := exists_outside_component_of_separation G L R u.val v.val
    hcover hinter hcross hR
  exact filledSide_isPlanar_of_outside_component G hG h2 L u v hne C hC

/-- The symmetric filled right side is planar as well. -/
theorem filledRight_isPlanar (hG : G.IsPlanar) (h2 : G.IsKConnected 2)
    (L R : Set V) (u v : R) (hne : u ≠ v)
    (hcover : L ∪ R = Set.univ) (hinter : L ∩ R = {u.val, v.val})
    (hcross : ∀ a ∈ L \ R, ∀ b ∈ R \ L, ¬G.Adj a b)
    (hL : (L \ R).Nonempty) :
    ((G.induce R) ⊔ edge u v).IsPlanar :=
  filledLeft_isPlanar G hG h2 R L u v hne (by rw [Set.union_comm, hcover])
    (by rw [Set.inter_comm, hinter])
    (fun a ha b hb hab => hcross b hb a ha hab.symm) hL

#print axioms exists_outside_component_of_separation
#print axioms filledLeft_isPlanar
#print axioms filledRight_isPlanar

end PlaneTopology.WagnerSeparatorSides
