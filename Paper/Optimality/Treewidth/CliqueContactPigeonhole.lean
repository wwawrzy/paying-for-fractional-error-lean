import Mathlib.Tactic

/-! Five nonempty rows with total size at most six contain two equal
singleton rows when all entries lie in a three-element set. -/
namespace Paper.CliqueContactPigeonhole
open scoped BigOperators

theorem four_singletons {A B : Type} [DecidableEq A] [DecidableEq B]
    (U : Finset A) (N : A → Finset B) (hU : U.card = 5)
    (hn : ∀ x ∈ U, (N x).Nonempty) (hs : (∑ x ∈ U, (N x).card) ≤ 6) :
    4 ≤ (U.filter (fun x => (N x).card = 1)).card := by
  have hp : ∀ x ∈ U, 2 ≤ (N x).card + if (N x).card = 1 then 1 else 0 := by
    intro x hx
    have hc := Finset.card_pos.mpr (hn x hx)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib] at hsum
  have hl : (∑ _x ∈ U, (2 : ℕ)) = 10 := by simp [hU]
  have hr : (∑ x ∈ U, if (N x).card = 1 then 1 else 0) =
      (U.filter (fun x => (N x).card = 1)).card := by simp
  rw [hl, hr] at hsum
  omega

theorem repeated_singleton {A B : Type} [DecidableEq A] [DecidableEq B]
    (U : Finset A) (D : Finset B) (N : A → Finset B)
    (hU : U.card = 5) (hD : D.card = 3)
    (hn : ∀ x ∈ U, (N x).Nonempty) (hsub : ∀ x ∈ U, N x ⊆ D)
    (hs : (∑ x ∈ U, (N x).card) ≤ 6) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ ∃ d ∈ D, N x = {d} ∧ N y = {d} := by
  let S := U.filter (fun x => (N x).card = 1)
  have hS : 4 ≤ S.card := four_singletons U N hU hn hs
  have ht : (D.image (fun d => ({d} : Finset B))).card < S.card := by
    have := Finset.card_image_le (s := D) (f := fun d => ({d} : Finset B))
    omega
  have hm : ∀ x ∈ S, N x ∈ D.image (fun d => ({d} : Finset B)) := by
    intro x hx
    obtain ⟨hxU, hxone⟩ := Finset.mem_filter.mp hx
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hxone
    have hdD : d ∈ D := hsub x hxU (by rw [hd]; exact Finset.mem_singleton_self d)
    exact Finset.mem_image.mpr ⟨d, hdD, hd.symm⟩
  obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht hm
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hx).2
  refine ⟨x, (Finset.mem_filter.mp hx).1, y, (Finset.mem_filter.mp hy).1, hne,
    d, ?_, hd, heq.symm.trans hd⟩
  exact hsub x (Finset.mem_filter.mp hx).1 (by rw [hd]; exact Finset.mem_singleton_self d)

end Paper.CliqueContactPigeonhole
#print axioms Paper.CliqueContactPigeonhole.four_singletons
#print axioms Paper.CliqueContactPigeonhole.repeated_singleton
