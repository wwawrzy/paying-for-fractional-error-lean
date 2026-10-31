import Mathlib

/-! Coordinate intervals of connected disjoint branch sets in a third power
of a path. This is purely finite combinatorics, with no planarity axiom. -/
namespace Paper.IntervalMinorModel
open scoped BigOperators

def GapConnected (S : Finset ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ k : ℤ, x < k → k+2 < y → ∃ z ∈ S, k ≤ z ∧ z ≤ k+2

structure Model (A : Type) where
  pieces : A → Finset ℤ
  nonempty : ∀ a, (pieces a).Nonempty
  disjoint : ∀ a b, a ≠ b → Disjoint (pieces a) (pieces b)
  gap : ∀ a, GapConnected (pieces a)

namespace Model
variable {A : Type} (M : Model A)

def low (a : A) : ℤ := (M.pieces a).min' (M.nonempty a)-3
def high (a : A) : ℤ := (M.pieces a).max' (M.nonempty a)

theorem low_le_high (a : A) : M.low a ≤ M.high a := by
  obtain ⟨z, hz⟩ := M.nonempty a
  have hl := Finset.min'_le (M.pieces a) z hz
  have hh := Finset.le_max' (M.pieces a) z hz
  dsimp [low, high]
  omega

theorem point_bounds {a : A} {z : ℤ} (hz : z ∈ M.pieces a) :
    M.low a ≤ z-3 ∧ z ≤ M.high a := by
  have hl := Finset.min'_le (M.pieces a) z hz
  have hh := Finset.le_max' (M.pieces a) z hz
  exact ⟨by dsimp [low]; omega, hh⟩

theorem meets_bag (a : A) (k : ℤ) (hl : M.low a ≤ k) (hh : k ≤ M.high a) :
    ∃ z ∈ M.pieces a, k ≤ z ∧ z ≤ k+3 := by
  let x := (M.pieces a).min' (M.nonempty a)
  let y := (M.pieces a).max' (M.nonempty a)
  have hx : x ∈ M.pieces a := Finset.min'_mem _ _
  have hy : y ∈ M.pieces a := Finset.max'_mem _ _
  change x-3 ≤ k at hl
  change k ≤ y at hh
  by_cases hkx : k ≤ x
  · exact ⟨x, hx, hkx, by omega⟩
  by_cases hky : y ≤ k+2
  · exact ⟨y, hy, hh, by omega⟩
  obtain ⟨z, hz, hzL, hzR⟩ := M.gap a x hx y hy k (by omega) (by omega)
  exact ⟨z, hz, hzL, by omega⟩

variable [Fintype A] [DecidableEq A]

def bag (k : ℤ) : Finset A := Finset.univ.filter (fun a => M.low a ≤ k ∧ k ≤ M.high a)

theorem bag_card (k : ℤ) : (M.bag k).card ≤ 4 := by
  classical
  have hw : ∀ a : M.bag k, ∃ z ∈ M.pieces a.val, k ≤ z ∧ z ≤ k+3 := by
    intro a
    have hh := (Finset.mem_filter.mp a.property).2
    exact M.meets_bag a.val k hh.1 hh.2
  let f : M.bag k → Fin 4 := fun a =>
    ⟨((hw a).choose-k).toNat, by have hh := (hw a).choose_spec; omega⟩
  have hf : Function.Injective f := by
    intro a b he
    by_contra hne
    have ha := (hw a).choose_spec
    have hb := (hw b).choose_spec
    have hh := congrArg Fin.val he
    dsimp [f] at hh
    have hz : (hw a).choose = (hw b).choose := by omega
    exact Finset.disjoint_left.mp (M.disjoint a.val b.val (fun h => hne (Subtype.ext h))) ha.1 (hz.symm ▸ hb.1)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

/-- Pull back a branch family along an injective relabeling. -/
def comap {B : Type} (f : B → A) (hf : Function.Injective f) : Model B where
  pieces b := M.pieces (f b)
  nonempty b := M.nonempty (f b)
  disjoint b c hbc := M.disjoint _ _ (fun h => hbc (hf h))
  gap b := M.gap (f b)

end Model
end Paper.IntervalMinorModel
