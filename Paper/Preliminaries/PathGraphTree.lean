import Paper.Preliminaries.ParentForest
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace Paper.PathGraphTree
open SimpleGraph

def parent (n : ℕ) (u : Fin n) : Option (Fin n) :=
  if h : 0 < u.val then some ⟨u.val - 1, by omega⟩ else none

theorem decrease (n : ℕ) (u v : Fin n) (h : parent n u = some v) : v.val < u.val := by
  unfold parent at h
  split_ifs at h with hu
  · have he := Option.some.inj h
    have hv := congrArg Fin.val he
    dsimp only at hv
    omega

theorem acyclic (n : ℕ) : (pathGraph n).IsAcyclic := by
  have hf := ParentForest.isAcyclic (parent n) Fin.val (decrease n)
  have hsub : pathGraph n ≤ ParentForest.graph (parent n) Fin.val (decrease n) := by
    intro u v huv
    rcases pathGraph_adj.mp huv with h | h
    · right
      change parent n v = some u
      rw [parent, dif_pos (by omega)]
      apply congrArg some
      apply Fin.ext
      dsimp only
      omega
    · left
      change parent n u = some v
      rw [parent, dif_pos (by omega)]
      apply congrArg some
      apply Fin.ext
      dsimp only
      omega
  exact hf.comap (Hom.ofLE hsub) Function.injective_id

theorem tree (n : ℕ) (hn : 0 < n) : (pathGraph n).IsTree := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨⟨pathGraph_preconnected n⟩, acyclic n⟩

theorem increasing_walk (n : ℕ) (i j : Fin n) (hij : i.val ≤ j.val) :
    ∃ p : (pathGraph n).Walk i j, ∀ r ∈ p.support, i.val ≤ r.val ∧ r.val ≤ j.val := by
  classical
  induction hdist : j.val - i.val using Nat.strongRecOn generalizing i with
  | ind m ih =>
    by_cases he : i = j
    · subst i
      refine ⟨.nil, ?_⟩
      intro r hr
      have he : r = j := by simpa only [Walk.support_nil, List.mem_singleton] using hr
      subst r
      exact ⟨le_rfl, le_rfl⟩
    have hlt : i.val < j.val := by have hv : i.val ≠ j.val := fun h => he (Fin.ext h); omega
    let next : Fin n := ⟨i.val + 1, by omega⟩
    have hnext : j.val - next.val < m := by dsimp only [next]; omega
    obtain ⟨p, hp⟩ := ih _ hnext next (by dsimp only [next]; omega) rfl
    have hadj : (pathGraph n).Adj i next := pathGraph_adj.mpr (Or.inl rfl)
    refine ⟨.cons hadj p, ?_⟩
    intro r hr
    rcases (by simpa only [Walk.support_cons, List.mem_cons] using hr) with he | hr
    · subst r
      exact ⟨le_rfl, hij⟩
    · have h := hp r hr
      dsimp only [next] at h
      omega

theorem path_interval (n : ℕ) {i j r : Fin n} (p : (pathGraph n).Walk i j) (hp : p.IsPath)
    (hr : r ∈ p.support) : min i.val j.val ≤ r.val ∧ r.val ≤ max i.val j.val := by
  classical
  have unique : ∀ (q : (pathGraph n).Walk i j), q.IsPath → q = p := by
    intro q hq
    exact congrArg Subtype.val ((acyclic n).path_unique ⟨q, hq⟩ ⟨p, hp⟩)
  by_cases hij : i.val ≤ j.val
  · obtain ⟨q, hq⟩ := increasing_walk n i j hij
    have he := unique q.toPath q.toPath.property
    have hmem : r ∈ q.support := q.support_toPath_subset (he.symm ▸ hr)
    simpa only [min_eq_left hij, max_eq_right hij] using hq r hmem
  · have hji : j.val ≤ i.val := le_of_not_ge hij
    obtain ⟨q, hq⟩ := increasing_walk n j i hji
    have he := unique q.reverse.toPath q.reverse.toPath.property
    have hmem : r ∈ q.reverse.support := q.reverse.support_toPath_subset (he.symm ▸ hr)
    have hm : r ∈ q.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hmem
    simpa only [min_eq_right hji, max_eq_left hji] using hq r hm

end Paper.PathGraphTree
