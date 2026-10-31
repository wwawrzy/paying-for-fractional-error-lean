import Paper.Preliminaries.CoreHierarchy
import Paper.Preliminaries.DepthOne

/-! Actual incidence graph and star assignment used to bound sunflower cores. -/
namespace Paper.CoreIncidence
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Candidate roles and set roles are distinct even when physically colocated. -/
def graph (H : Finset (Finset V)) : SimpleGraph (V ⊕ H) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inr s => v ∈ s.val
    | Sum.inr s, Sum.inl v => v ∈ s.val
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := ⟨by intro x; cases x <;> simp⟩

noncomputable def centers (H : Finset (Finset V)) (O : Finset V) : Finset (V ⊕ H) :=
  O.image Sum.inl

noncomputable def markers (H : Finset (Finset V)) (X : Finset V) : Finset (V ⊕ H) :=
  X.image Sum.inl

theorem markers_disjoint_covered (H : Finset (Finset V)) (O X : Finset V)
    (hXO : Disjoint X O) : Disjoint (markers H X) (covered (graph H) (centers H O)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hc
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
  rcases (mem_closed (graph H) _ _).mp hxw with he | ha
  · have he' : v = d := Sum.inl.inj he
    exact Finset.disjoint_left.mp hXO hv (he'.symm ▸ hd)
  · exact ha

theorem set_covered (H : Finset (Finset V)) (O : Finset V)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) (s : H) :
    Sum.inr s ∈ covered (graph H) (centers H O) := by
  obtain ⟨d, hd⟩ := hO s.val s.property
  refine Finset.mem_biUnion.mpr ⟨Sum.inl d,
    Finset.mem_image.mpr ⟨d, (Finset.mem_inter.mp hd).2, rfl⟩, ?_⟩
  exact (mem_closed (graph H) _ _).mpr (Or.inr (Finset.mem_inter.mp hd).1)

/-- Every assigned set has a genuine owner in O which belongs to the set. -/
theorem owner_set (H : Finset (Finset V)) (O : Finset V)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) (s : H) :
    ∃ d ∈ O, StarMinor.owner (graph H) (centers H O) (Sum.inr s) = Sum.inl d ∧ d ∈ s.val := by
  classical
  have hm := StarMinor.owner_covered (graph H) (centers H O) (set_covered H O hO s)
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  refine ⟨d, hd, he.symm, ?_⟩
  have hs := StarMinor.owner_star (graph H) (centers H O) (Sum.inr s)
  rw [← he] at hs
  rcases hs with hn | ha
  · cases hn
  · exact ha

/-- Different sunflower witnesses have different assigned owners when their
common core avoids O. This protects the count from parallel-edge collapse. -/
theorem owners_injective (H F : Finset (Finset V)) (O C : Finset V)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) (hF : F ⊆ H)
    (hsun : Sunflower.IsSunflower F C) (hCO : Disjoint C O) :
    Set.InjOn (fun s : H => StarMinor.owner (graph H) (centers H O) (Sum.inr s))
      {s : H | s.val ∈ F} := by
  intro s hs t ht heq
  by_contra hn
  have hne : s.val ≠ t.val := fun he => hn (Subtype.ext he)
  obtain ⟨d, hd, hsown, hds⟩ := owner_set H O hO s
  obtain ⟨e, he, htow, het⟩ := owner_set H O hO t
  have hde : d = e := Sum.inl.inj (hsown.symm.trans (heq.trans htow))
  have hdt : d ∈ t.val := hde.symm ▸ het
  have hdC : d ∈ C := (hsun s.val hs t.val ht hne) ▸ Finset.mem_inter.mpr ⟨hds, hdt⟩
  exact Finset.disjoint_left.mp hCO hdC hd
end Paper.CoreIncidence
