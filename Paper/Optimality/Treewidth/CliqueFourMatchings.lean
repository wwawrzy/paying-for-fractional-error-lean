import GraphTheory.SimpleGraph.Degeneracy
import Mathlib.Tactic.FinCases

/-! The three perfect matchings on four labeled vertices. A graph of
minimum degree two contains at least two of them. The finite numerical
step is kernel-decided over six bits, while the actual graph API bridge
uses degree counts and adjacency symmetry explicitly. -/
namespace Paper.CliqueFourMatchings

open SimpleGraph

def ends : Fin 3 → (Fin 4 × Fin 4) × (Fin 4 × Fin 4) :=
  ![((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]

def part (k : Fin 3) (side : Bool) : Finset (Fin 4) :=
  if side then {(ends k).2.1, (ends k).2.2} else {(ends k).1.1, (ends k).1.2}

theorem part_card : ∀ k side, (part k side).card = 2 := by decide

theorem part_partition : ∀ k, Disjoint (part k false) (part k true) ∧
    part k false ∪ part k true = Finset.univ := by decide

private theorem pair_label_indices : ∀ a b : Fin 4, a ≠ b →
    ∃! k : Fin 3, ({a, b} : Finset (Fin 4)) = part k false ∨ {a, b} = part k true := by
  unfold ExistsUnique
  decide

theorem pair_label (T : Finset (Fin 4)) (hT : T.card = 2) :
    ∃! k : Fin 3, T = part k false ∨ T = part k true := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
  exact pair_label_indices a b hab

def available (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj] : Finset (Fin 3) :=
  Finset.univ.filter (fun k =>
    H.Adj (ends k).1.1 (ends k).1.2 ∧ H.Adj (ends k).2.1 (ends k).2.2)

private def weight (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj] (i j : Fin 4) : ℕ :=
  if H.Adj i j then 1 else 0

private theorem numeric : ∀ a b c d e f : Fin 2,
    2 ≤ a.val + b.val + c.val → 2 ≤ a.val + d.val + e.val →
    2 ≤ b.val + d.val + f.val → 2 ≤ c.val + e.val + f.val →
    2 ≤ a.val * f.val + b.val * e.val + c.val * d.val := by decide

variable (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj]

private theorem weight_self (i : Fin 4) : weight H i i = 0 := by simp [weight]

private theorem weight_symm (i j : Fin 4) : weight H i j = weight H j i := by
  by_cases h : H.Adj i j
  · simp only [weight, if_pos h, if_pos h.symm]
  · simp only [weight, if_neg h, if_neg (fun hh : H.Adj j i => h hh.symm)]

private theorem degree_sum (i : Fin 4) :
    H.degree i = weight H i 0 + weight H i 1 + weight H i 2 + weight H i 3 := by
  have hh : H.degree i = ∑ j : Fin 4, weight H i j := by
    unfold weight
    rw [Finset.sum_boole]
    change (H.neighborFinset i).card = (Finset.univ.filter (H.Adj i)).card
    congr 1
    ext j
    simp only [H.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [Fin.sum_univ_four] using hh

private theorem pair_weight (a b c d : Fin 4) :
    (if H.Adj a b ∧ H.Adj c d then 1 else 0 : ℕ) = weight H a b * weight H c d := by
  by_cases hab : H.Adj a b <;> by_cases hcd : H.Adj c d <;> simp [weight, hab, hcd]

private theorem card_available : (available H).card =
    weight H 0 1 * weight H 2 3 + weight H 0 2 * weight H 1 3 +
      weight H 0 3 * weight H 1 2 := by
  have hh : (∑ k : Fin 3,
      if H.Adj (ends k).1.1 (ends k).1.2 ∧ H.Adj (ends k).2.1 (ends k).2.2
        then (1 : ℕ) else 0) = (available H).card := by
    simpa only [available, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun k : Fin 3 =>
        H.Adj (ends k).1.1 (ends k).1.2 ∧ H.Adj (ends k).2.1 (ends k).2.2) Finset.univ)
  rw [← hh, Fin.sum_univ_three]
  change (if H.Adj 0 1 ∧ H.Adj 2 3 then 1 else 0) +
    (if H.Adj 0 2 ∧ H.Adj 1 3 then 1 else 0) +
    (if H.Adj 0 3 ∧ H.Adj 1 2 then 1 else 0) = _
  rw [pair_weight, pair_weight, pair_weight]

theorem at_least_two (hd : ∀ i, 2 ≤ H.degree i) : 2 ≤ (available H).card := by
  have bound (i j : Fin 4) : weight H i j < 2 := by unfold weight; split <;> decide
  let a : Fin 2 := ⟨weight H 0 1, bound _ _⟩
  let b : Fin 2 := ⟨weight H 0 2, bound _ _⟩
  let c : Fin 2 := ⟨weight H 0 3, bound _ _⟩
  let d : Fin 2 := ⟨weight H 1 2, bound _ _⟩
  let e : Fin 2 := ⟨weight H 1 3, bound _ _⟩
  let f : Fin 2 := ⟨weight H 2 3, bound _ _⟩
  have h0 := degree_sum H 0
  have h1 := degree_sum H 1
  have h2 := degree_sum H 2
  have h3 := degree_sum H 3
  rw [weight_self, zero_add] at h0
  rw [weight_symm H 1 0, weight_self, add_zero] at h1
  rw [weight_symm H 2 0, weight_symm H 2 1, weight_self, add_zero] at h2
  rw [weight_symm H 3 0, weight_symm H 3 1, weight_symm H 3 2, weight_self, add_zero] at h3
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  rw [card_available]
  exact numeric a b c d e f (by change 2 ≤ weight H 0 1 + weight H 0 2 + weight H 0 3; omega)
    (by change 2 ≤ weight H 0 1 + weight H 1 2 + weight H 1 3; omega)
    (by change 2 ≤ weight H 0 2 + weight H 1 2 + weight H 2 3; omega)
    (by change 2 ≤ weight H 0 3 + weight H 1 3 + weight H 2 3; omega)

end Paper.CliqueFourMatchings

#print axioms Paper.CliqueFourMatchings.at_least_two
#print axioms Paper.CliqueFourMatchings.part_card
#print axioms Paper.CliqueFourMatchings.part_partition
#print axioms Paper.CliqueFourMatchings.pair_label
