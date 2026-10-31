import Paper.Preliminaries.ParentForest

/-! Nearest marked ancestors in a finite ranked parent forest. -/
namespace Paper.ForestRegions
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]
variable (parent : V → Option V) (rank : V → ℕ)
variable (decrease : ∀ u v, parent u = some v → rank v < rank u)

noncomputable def owner (parent : V → Option V) (rank : V → ℕ)
    (decrease : ∀ u v, parent u = some v → rank v < rank u) (X : Finset V) (u : V) : Option V :=
  if u ∈ X then some u else
    match h : parent u with
    | none => none
    | some v => owner parent rank decrease X v
termination_by rank u
decreasing_by exact decrease u v h

theorem owner_center (X : Finset V) {x : V} (hx : x ∈ X) :
    owner parent rank decrease X x = some x := by
  rw [owner]
  simp only [if_pos hx]

theorem owner_parent (X : Finset V) {u v : V} (hu : u ∉ X) (hp : parent u = some v) :
    owner parent rank decrease X u = owner parent rank decrease X v := by
  rw [owner, if_neg hu]
  split
  · simp_all
  · rename_i w hw
    have he : w = v := Option.some.inj (hw.symm.trans hp)
    subst w
    rfl

theorem owner_step (X : Finset V) {u x : V} (hu : u ∉ X)
    (h : owner parent rank decrease X u = some x) :
    ∃ v, parent u = some v ∧ owner parent rank decrease X v = some x := by
  rw [owner, if_neg hu] at h
  split at h
  · contradiction
  · exact ⟨_, ‹parent u = some _›, h⟩

theorem owner_mem (X : Finset V) {u x : V}
    (h : owner parent rank decrease X u = some x) : x ∈ X := by
  induction hu : rank u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hx : u ∈ X
    · rw [owner_center parent rank decrease X hx] at h
      exact (Option.some.inj h) ▸ hx
    · obtain ⟨v, hp, hv⟩ := owner_step parent rank decrease X hx h
      exact ih (rank v) (by have hh := decrease u v hp; omega) hv rfl

theorem owner_rank (X : Finset V) {u x : V}
    (h : owner parent rank decrease X u = some x) : rank x ≤ rank u := by
  induction hu : rank u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hx : u ∈ X
    · rw [owner_center parent rank decrease X hx] at h
      have he := Option.some.inj h
      subst x
      omega
    · obtain ⟨v, hp, hv⟩ := owner_step parent rank decrease X hx h
      have hh := ih (rank v) (by have hh := decrease u v hp; omega) hv rfl
      have hd := decrease u v hp
      omega

theorem connected (X : Finset V) {x : V} (hx : x ∈ X) :
    ((ParentForest.graph parent rank decrease).induce
      {u | owner parent rank decrease X u = some x}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, owner_center parent rank decrease X hx⟩, ?_⟩
  intro u
  have reach : ∀ (v : V) (hv : owner parent rank decrease X v = some x),
      ((ParentForest.graph parent rank decrease).induce
        {u | owner parent rank decrease X u = some x}).Reachable
        ⟨x, owner_center parent rank decrease X hx⟩ ⟨v, hv⟩ := by
    intro v
    induction hn : rank v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      intro hv
      by_cases hvX : v ∈ X
      · have he : v = x := by
          rw [owner_center parent rank decrease X hvX] at hv
          exact Option.some.inj hv
        subst v
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨w, hp, hw⟩ := owner_step parent rank decrease X hvX hv
        have hr := ih (rank w) (by have hh := decrease v w hp; omega) w rfl hw
        have ha : ((ParentForest.graph parent rank decrease).induce
            {u | owner parent rank decrease X u = some x}).Adj ⟨w, hw⟩ ⟨v, hv⟩ :=
          Or.inr hp
        exact hr.trans ha.reachable
  exact reach u.val u.property
end Paper.ForestRegions
