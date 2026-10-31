import Paper.Optimality.Treewidth.PathPowerTreewidth
import Paper.Preliminaries.SevenFoundation

namespace Paper.PathPowerCounting
open SevenFoundation PathPowerTreewidth
open scoped BigOperators

theorem mem_closed_iff (n t : ℕ) (u v : Fin n) :
    u ∈ closed (graph n t) v ↔ u.val ≤ v.val + t ∧ v.val ≤ u.val + t := by
  rw [mem_closed]
  constructor
  · rintro (rfl | h)
    · omega
    · exact ⟨h.2.2, h.2.1⟩
  · intro h
    by_cases he : u = v
    · exact Or.inl he
    · exact Or.inr ⟨Ne.symm he, h.2, h.1⟩

theorem closed_card (n t : ℕ) (v : Fin n) : (closed (graph n t) v).card ≤ 2 * t + 1 := by
  let f : closed (graph n t) v → Fin (2 * t + 1) := fun u =>
    ⟨u.val.val + t - v.val, by have h := (mem_closed_iff n t u.val v).mp u.property; omega⟩
  have hf : Function.Injective f := by
    intro u w he
    apply Subtype.ext
    apply Fin.ext
    have hu := (mem_closed_iff n t u.val v).mp u.property
    have hw := (mem_closed_iff n t w.val v).mp w.property
    have hh := congrArg Fin.val he
    dsimp only [f] at hh
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem domination_count (n t : ℕ) (D : Finset (Fin n)) (hD : dominates (graph n t) D) :
    n ≤ (2 * t + 1) * D.card := by
  have he : covered (graph n t) D = Finset.univ := by
    ext v
    exact ⟨fun _ => Finset.mem_univ _, fun _ => hD v⟩
  calc
    n = (covered (graph n t) D).card := by rw [he, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ v ∈ D, (closed (graph n t) v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ D, (2 * t + 1) := Finset.sum_le_sum (fun v _ => closed_card n t v)
    _ = _ := by simp [mul_comm]

end Paper.PathPowerCounting
