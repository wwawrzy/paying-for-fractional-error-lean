import Paper.Preliminaries.SmallNumberCode

/-! Fixed bounded distance ranks and their local Bellman update. -/
namespace Paper.ClippedRank

abbrev Rank (D : ℕ) := Fin (D + 2)

def top (D : ℕ) : Rank D := ⟨D + 1, by omega⟩

def next (D : ℕ) (r : Rank D) : Rank D :=
  ⟨min (r.val + 1) (D + 1), by have := min_le_right (r.val + 1) (D + 1); omega⟩

theorem next_le (D : ℕ) (r : Rank D) : (next D r).val ≤ r.val + 1 := min_le_left _ _

theorem next_finite (D : ℕ) (r : Rank D) (h : (next D r).val < D + 1) :
    (next D r).val = r.val + 1 ∧ r.val < D + 1 := by
  change min (r.val + 1) (D + 1) < D + 1 at h
  have hr : r.val + 1 < D + 1 := (min_lt_iff).mp h |>.resolve_right (by omega)
  exact ⟨min_eq_left (by omega), by omega⟩

def choose {V : Type} (D : ℕ) (N : Finset V) (self : Rank D) (incoming : N → Rank D) : Rank D :=
  (insert self (N.attach.image (fun w => next D (incoming w)))).min'
    (Finset.insert_nonempty _ _)

theorem choose_le_self {V : Type} (D : ℕ) (N : Finset V) (self : Rank D)
    (incoming : N → Rank D) : choose D N self incoming ≤ self :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem choose_le_neighbor {V : Type} (D : ℕ) (N : Finset V) (self : Rank D)
    (incoming : N → Rank D) (w : N) : (choose D N self incoming).val ≤ (incoming w).val + 1 := by
  have hh : choose D N self incoming ≤ next D (incoming w) :=
    Finset.min'_le _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩)))
  have hv : (choose D N self incoming).val ≤ (next D (incoming w)).val := hh
  exact hv.trans (next_le D (incoming w))

theorem choose_origin {V : Type} (D : ℕ) (N : Finset V) (self : Rank D)
    (incoming : N → Rank D) : choose D N self incoming = self ∨
      ∃ w : N, choose D N self incoming = next D (incoming w) := by
  have hm := Finset.min'_mem (insert self (N.attach.image (fun w => next D (incoming w))))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact Or.inl hm
  · obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hm
    exact Or.inr ⟨w, hw.symm⟩
end Paper.ClippedRank
