import Paper.Averaging.Tasks.FiniteIncidenceAverage

/-! A capped genuine multi-source shortest-path level, and a small level
set. These are the finite BFS ingredients for the connecting-set lemma. -/
namespace Paper.SeparatorLayers
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def values (X : Finset V) (r : ℕ) (u : V) : Finset ℕ :=
  insert r ((X.filter (fun x => G.Reachable x u)).image (fun x => G.dist x u))

noncomputable def level (X : Finset V) (r : ℕ) (u : V) : ℕ :=
  (values G X r u).min' ⟨r, Finset.mem_insert_self _ _⟩

theorem level_le_cap (X : Finset V) (r : ℕ) (u : V) : level G X r u ≤ r :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem level_le_dist (X : Finset V) (r : ℕ) {x u : V} (hx : x ∈ X) (hr : G.Reachable x u) :
    level G X r u ≤ G.dist x u :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨x, Finset.mem_filter.mpr ⟨hx, hr⟩, rfl⟩))

theorem realized (X : Finset V) (r : ℕ) {u : V} (hu : level G X r u < r) :
    ∃ x ∈ X, G.Reachable x u ∧ G.dist x u = level G X r u := by
  have hm := Finset.min'_mem (values G X r u) ⟨r, Finset.mem_insert_self _ _⟩
  change level G X r u ∈ values G X r u at hm
  rcases Finset.mem_insert.mp hm with he | hi
  · exact False.elim (by omega)
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hi
    exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2, he⟩

theorem source_zero (X : Finset V) (r : ℕ) {u : V} (hu : u ∈ X) : level G X r u = 0 := by
  have hh := level_le_dist G X r hu (SimpleGraph.Reachable.refl u)
  have hz : G.dist u u = 0 := by simp
  omega

theorem edge_step (X : Finset V) (r : ℕ) {u v : V} (ha : G.Adj u v) :
    level G X r v ≤ level G X r u + 1 := by
  by_cases hu : level G X r u < r
  · obtain ⟨x, hx, hxu, hdist⟩ := realized G X r hu
    obtain ⟨p, hp⟩ := hxu.exists_walk_length_eq_dist
    have hxv : G.Reachable x v := hxu.trans ha.reachable
    have hh := level_le_dist G X r hx hxv
    have hd := SimpleGraph.dist_le (p.append ha.toWalk)
    simp only [SimpleGraph.Walk.length_append] at hd
    change G.dist x v ≤ p.length + 1 at hd
    omega
  · have hh := level_le_cap G X r v
    omega

noncomputable def layer (rank : V → ℕ) (j : ℕ) : Finset V := Finset.univ.filter (fun v => rank v = j)

theorem small_layer (rank : V → ℕ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ j : Fin r, r * (layer rank j.val).card ≤ Fintype.card V := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hsum : (∑ j : Fin r, (layer rank j.val).card) ≤ Fintype.card V := by
    have he' : (∑ j : Fin r, (layer rank j.val).card) =
        ∑ v : V, ((Finset.univ : Finset (Fin r)).filter (fun j => rank v = j.val)).card := by
      calc
        _ = ∑ j : Fin r, ((Finset.univ : Finset V).filter (fun v => rank v = j.val)).card := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
        _ = _ := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          exact Finset.sum_comm
    rw [he']
    calc
      _ ≤ ∑ _v : V, 1 := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.card_le_one.mpr
        intro i hi j hj
        exact Fin.ext ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
      _ = _ := by simp
  by_contra hn
  push Not at hn
  have hlow : r * Fintype.card V < r * (∑ j : Fin r, (layer rank j.val).card) := by
    calc
      _ = ∑ _j : Fin r, Fintype.card V := by simp
      _ < ∑ j : Fin r, r * (layer rank j.val).card := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
        intro j _
        exact hn j
      _ = _ := by rw [Finset.mul_sum]
  have hh := Nat.mul_le_mul_left r hsum
  omega
end Paper.SeparatorLayers
