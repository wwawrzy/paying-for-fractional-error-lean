import Paper.Partitions.Separators.BfsSeparator
import Paper.Preliminaries.WeakProjection

/-! The actual layered graph used to connect m+1 terminal sets through m
copies of the physical graph. Vertical edges are allowed only at terminals. -/
namespace Paper.LayeredConnector
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def graph {m : ℕ} (A : Fin (m + 1) → Finset V) : SimpleGraph (V × Fin m) where
  Adj x y := (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
    (x.1 = y.1 ∧ ((x.2.val + 1 = y.2.val ∧ x.1 ∈ A y.2.castSucc) ∨
      (y.2.val + 1 = x.2.val ∧ x.1 ∈ A x.2.castSucc)))
  symm := by
    rintro x y (⟨hl, ha⟩ | ⟨hv, h⟩)
    · exact Or.inl ⟨hl.symm, ha.symm⟩
    · right
      refine ⟨hv.symm, ?_⟩
      rcases h with ⟨hl, hm⟩ | ⟨hl, hm⟩
      · exact Or.inr ⟨hl, hv ▸ hm⟩
      · exact Or.inl ⟨hl, hv ▸ hm⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_, ha⟩ | ⟨_, h⟩
    · exact ha.ne rfl
    · rcases h with h | h <;> omega⟩

theorem weak_edges {m : ℕ} (A : Fin (m + 1) → Finset V) (x y : V × Fin m)
    (h : (graph G A).Adj x y) : x.1 = y.1 ∨ G.Adj x.1 y.1 := by
  rcases h with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

def horizontal {m : ℕ} (A : Fin (m + 1) → Finset V) (j : Fin m) : G →g graph G A where
  toFun v := (v, j)
  map_rel' h := Or.inl ⟨rfl, h⟩

theorem walk_cross_cut {U : Type*} (J : SimpleGraph U) (Q : U → Prop) {u v : U}
    (p : J.Walk u v) (hu : Q u) (hv : ¬ Q v) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, J.Adj x y ∧ Q x ∧ ¬ Q y := by
  classical
  revert hu hv
  induction p with
  | nil => intro hu hv; exact False.elim (hv hu)
  | @cons u w v ha p ih =>
    intro hu hv
    by_cases hw : Q w
    · obtain ⟨x, hx, y, hy, hxy, hQx, hQy⟩ := ih hw hv
      exact ⟨x, by simp [hx], y, by simp [hy], hxy, hQx, hQy⟩
    · exact ⟨u, by simp, w, by simp [p.start_mem_support], ha, hu, hw⟩

theorem internal_terminal {m : ℕ} (A : Fin (m + 1) → Finset V) {x y : V × Fin m}
    (p : (graph G A).Walk x y) (i : Fin (m + 1))
    (hx : x.2.val < i.val) (hy : i.val ≤ y.2.val) :
    ∃ z ∈ p.support, z.1 ∈ A i := by
  obtain ⟨u, hu, v, hv, hadj, hul, hvl⟩ := walk_cross_cut (graph G A) (fun z => z.2.val < i.val) p hx (by omega)
  rcases hadj with ⟨he, _⟩ | ⟨he, hvv⟩
  · have hh := congrArg Fin.val he
    omega
  · rcases hvv with ⟨hl, hm⟩ | ⟨hl, hm⟩
    · have hindex : v.2.castSucc = i := Fin.ext (by dsimp at hul hvl hl ⊢; omega)
      exact ⟨u, hu, hindex ▸ hm⟩
    · omega
end Paper.LayeredConnector
