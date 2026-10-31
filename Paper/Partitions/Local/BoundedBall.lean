import Mathlib

/-! Explicit finite graph balls and a uniform count of connected small sets.
The coarse bound (Δ+1)^k suffices and avoids any graph-size dependence. -/
namespace Paper.BoundedBall
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def ball (v : V) : ℕ → Finset V
  | 0 => {v}
  | r + 1 => ball v r ∪ (ball v r).biUnion (fun u => G.neighborFinset u)

theorem step (v : V) (r : ℕ) : ball G v r ⊆ ball G v (r + 1) := Finset.subset_union_left

theorem mono (v : V) {r s : ℕ} (hrs : r ≤ s) : ball G v r ⊆ ball G v s := by
  induction s, hrs using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ s _ ih => exact ih.trans (step G v s)

theorem neighbor (v : V) (r : ℕ) {u w : V} (hu : u ∈ ball G v r) (ha : G.Adj u w) :
    w ∈ ball G v (r + 1) :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu, (G.mem_neighborFinset u w).mpr ha⟩)

theorem walk_mem {u v : V} (p : G.Walk u v) : v ∈ ball G u p.length := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [ball]
  | Hconcat p h ih => simpa only [SimpleGraph.Walk.length_concat] using neighbor G _ _ ih h

theorem card_bound (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) (r : ℕ) :
    (ball G v r).card ≤ (Δ + 1) ^ r := by
  induction r with
  | zero => simp [ball]
  | succ r ih =>
    have hb : ((ball G v r).biUnion (fun u => G.neighborFinset u)).card ≤ Δ * (ball G v r).card := by
      calc
        _ ≤ ∑ u ∈ ball G v r, (G.neighborFinset u).card := Finset.card_biUnion_le
        _ = ∑ u ∈ ball G v r, G.degree u := by simp only [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ ∑ _u ∈ ball G v r, Δ := Finset.sum_le_sum (fun u _ => hdeg u)
        _ = _ := by simp [mul_comm]
    calc
      _ ≤ (ball G v r).card + ((ball G v r).biUnion (fun u => G.neighborFinset u)).card := Finset.card_union_le _ _
      _ ≤ (Δ + 1) * (ball G v r).card := by nlinarith
      _ ≤ (Δ + 1) * (Δ + 1) ^ r := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ, Nat.mul_comm]

theorem contains_connected (S : Finset V) (hS : (G.induce (S : Set V)).Connected)
    (k : ℕ) (hsize : S.card ≤ k) (v : V) (hv : v ∈ S) : S ⊆ ball G v k := by
  intro u hu
  obtain ⟨p, hp⟩ := (hS ⟨v, hv⟩ ⟨u, hu⟩).exists_isPath
  have hlen : p.length < S.card := by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hp.length_lt
  let f : G.induce (S : Set V) →g G := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  have hmem := walk_mem G (p.map f)
  have hlength : (p.map f).length ≤ k := by rw [SimpleGraph.Walk.length_map]; omega
  exact mono G v hlength hmem

noncomputable def smallContaining (v : V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun S => v ∈ S ∧ (G.induce (S : Set V)).Connected ∧ S.card ≤ k)

theorem small_count (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) (k : ℕ) :
    (smallContaining G v k).card ≤ 2 ^ ((Δ + 1) ^ k) := by
  have hsub : smallContaining G v k ⊆ (ball G v k).powerset := by
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    exact Finset.mem_powerset.mpr (contains_connected G S hh.2.1 k hh.2.2 v hh.1)
  calc
    _ ≤ (ball G v k).powerset.card := Finset.card_le_card hsub
    _ = 2 ^ (ball G v k).card := Finset.card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (card_bound G Δ hdeg v k)
end Paper.BoundedBall
