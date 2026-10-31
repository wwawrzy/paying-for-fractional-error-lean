import Paper.Partitions.Separators.SeparatorLayers

/-! Actual shortest walks or a small BFS layer meeting every X-to-Y walk.
This is the two-terminal ingredient of the connecting-set dichotomy. -/
namespace Paper.BfsSeparator
attribute [local instance] Classical.propDecidable
open SeparatorLayers
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem walk_level_lt (rank : V → ℕ) (hstep : ∀ u v, G.Adj u v → rank v ≤ rank u + 1)
    (j : ℕ) {u v : V} (p : G.Walk u v)
    (havoid : ∀ z ∈ p.support, rank z ≠ j) (hu : rank u < j) : rank v < j := by
  revert havoid hu
  induction p with
  | nil => intro _ hu; exact hu
  | @cons u w v hadj p ih =>
    intro havoid hu
    have ht : ∀ z ∈ p.support, rank z ≠ j := by
      intro z hz
      exact havoid z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)
    have hn := ht w p.start_mem_support
    have hh := hstep u w hadj
    exact ih ht (by omega)

theorem short_walk_or_layer (X Y : Finset V) (r : ℕ) (hr : 1 ≤ r) :
    (∃ x ∈ X, ∃ y ∈ Y, ∃ p : G.Walk x y, p.length + 1 ≤ r) ∨
      ∃ Z : Finset V, r * Z.card ≤ Fintype.card V ∧
        ∀ x ∈ X, ∀ y ∈ Y, ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ Z := by
  classical
  by_cases hshort : ∃ y ∈ Y, level G X r y < r
  · left
    obtain ⟨y, hy, hlev⟩ := hshort
    obtain ⟨x, hx, hreach, he⟩ := realized G X r hlev
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    exact ⟨x, hx, y, hy, p, by omega⟩
  · right
    obtain ⟨j, hj⟩ := small_layer (level G X r) r hr
    refine ⟨layer (level G X r) j.val, hj, ?_⟩
    intro x hx y hy p
    by_contra hn
    push Not at hn
    have havoid : ∀ z ∈ p.support, level G X r z ≠ j.val := by
      intro z hz he
      exact hn z hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    have hx0 := source_zero G X r hx
    have hycap : level G X r y = r := by
      have hh : ¬ level G X r y < r := fun h => hshort ⟨y, hy, h⟩
      have hc := level_le_cap G X r y
      omega
    by_cases hj0 : j.val = 0
    · exact havoid x p.start_mem_support (hx0.trans hj0.symm)
    · have hlt := walk_level_lt G (level G X r) (fun _ _ h => edge_step G X r h) j.val p havoid (by omega)
      have hh := j.isLt
      omega
end Paper.BfsSeparator
