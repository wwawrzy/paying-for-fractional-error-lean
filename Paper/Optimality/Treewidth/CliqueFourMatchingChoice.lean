import Paper.Optimality.Treewidth.CliqueFourMatchings
import Mathlib.Combinatorics.Pigeonhole

/-! Choose an available four-vertex matching with at most one deficient
attachment. Each two-neighbor row belongs to exactly one of the three
matchings; the strict crossing count controls the two-choice case. -/
namespace Paper.CliqueFourMatchingChoice

open CliqueFourMatchings

def bad (N : Fin 4 → Finset (Fin 4)) (k : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter (fun a => N a = part k false ∨ N a = part k true)

theorem choose (N : Fin 4 → Finset (Fin 4)) (A : Finset (Fin 3))
    (hA : 2 ≤ A.card)
    (hsmall : A.card < 3 → (Finset.univ.filter (fun a => (N a).card = 2)).card ≤ 3) :
    ∃ k ∈ A, (bad N k).card ≤ 1 := by
  classical
  let S := Finset.univ.filter (fun a => (N a).card = 2)
  let f : Fin 4 → Fin 3 := fun a =>
    if h : (N a).card = 2 then Classical.choose (pair_label (N a) h) else 0
  have hfiber (k : Fin 3) : S.filter (fun a => f a = k) = bad N k := by
    ext a
    simp only [S, bad, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h2, hk⟩
      have hchoice := (Classical.choose_spec (pair_label (N a) h2)).1
      have heq : f a = Classical.choose (pair_label (N a) h2) := by
        dsimp only [f]
        rw [dif_pos h2]
      rw [← heq, hk] at hchoice
      exact hchoice
    · intro hk
      have h2 : (N a).card = 2 := by
        rcases hk with hh | hh
        · rw [hh]
          exact part_card k false
        · rw [hh]
          exact part_card k true
      refine ⟨h2, ?_⟩
      dsimp only [f]
      rw [dif_pos h2]
      exact ((Classical.choose_spec (pair_label (N a) h2)).2 k hk).symm
  have hS : S.card ≤ 4 := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hlt : S.card < A.card * 2 := by
    by_cases hfull : 3 ≤ A.card
    · have hh := Nat.mul_le_mul_right 2 hfull
      omega
    · have hh : S.card ≤ 3 := hsmall (by omega)
      have hm := Nat.mul_le_mul_right 2 hA
      omega
  obtain ⟨k, hk, hcard⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f) hlt
  refine ⟨k, hk, ?_⟩
  rw [hfiber] at hcard
  omega

end Paper.CliqueFourMatchingChoice

#print axioms Paper.CliqueFourMatchingChoice.choose
