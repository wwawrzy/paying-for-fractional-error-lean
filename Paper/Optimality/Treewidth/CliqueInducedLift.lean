import Paper.Optimality.Treewidth.CliqueComponentBoundary

/-! Lift an actual minor model from an induced graph while retaining
the precise original-vertex branch sets and their containment. -/
namespace Paper.CliqueInducedLift

open SimpleGraph
variable {V U : Type} (G : SimpleGraph V) {H : SimpleGraph U}

noncomputable def model (A : Set V) (m : MinorModel H (G.induce A)) : MinorModel H G where
  branchSet a := Subtype.val '' m.branchSet a
  nonempty a := (m.nonempty a).image Subtype.val
  disjoint a b hab := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxy : x = y := Subtype.ext (hxz.trans hyz.symm)
    exact (m.disjoint a b hab).ne_of_mem hx hy hxy
  connected a := by
    let f : ((G.induce A).induce (m.branchSet a)) →g
        G.induce (Subtype.val '' m.branchSet a) :=
      { toFun := fun z => ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
        map_rel' := fun h => h }
    have hf : Function.Surjective f := by
      rintro ⟨z, w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    exact Connected.map f hf (m.connected a)
  adjacent a b hab := by
    obtain ⟨x, hx, y, hy, hxy⟩ := m.adjacent a b hab
    exact ⟨x.val, ⟨x, hx, rfl⟩, y.val, ⟨y, hy, rfl⟩, hxy⟩

theorem branch_subset (A : Set V) (m : MinorModel H (G.induce A)) (a : U) :
    (model G A m).branchSet a ⊆ A := by
  rintro z ⟨x, _, rfl⟩
  exact x.property

end Paper.CliqueInducedLift

#print axioms Paper.CliqueInducedLift.model
#print axioms Paper.CliqueInducedLift.branch_subset
