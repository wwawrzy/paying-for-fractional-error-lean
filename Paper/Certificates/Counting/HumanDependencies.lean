import Paper.Initialization.Pruning.InitialForest
import Paper.Certificates.Counting.PartialOptimum
import Paper.Certificates.Counting.WeightedCertificate

/-! Exact source-level dependencies: attained weighted partial optimum with
ceil(a) orientation, multicover certificate, and the forest lemma for any
d-degenerate graph (not only graphs with an extra density hypothesis). -/
namespace Paper.HumanDependencies
attribute [local instance] Classical.propDecidable
open SevenFoundation InitialForest
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem integral_optimum (a : ℝ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ D : Finset V, R ⊆ covered G D ∧
      (∑ v ∈ D, c v) ≤ (2*(Nat.ceil a : ℝ)+1)*PartialOptimum.number G R c := by
  let p := Nat.ceil a
  have hpa : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by exact_mod_cast (ha.trans hpa)
  have hnat (S : Finset V) : G.inducedEdgeCount S ≤ p*S.card := by
    have hh := (MinorDensity.induced_bound G hden S).trans
      (mul_le_mul_of_nonneg_right hpa (Nat.cast_nonneg _))
    exact_mod_cast hh
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G R c hc
  obtain ⟨D, hD, hb⟩ := WeightedIntegrality.exists_integral_cover G R p hp hnat c x hc hx.1 hx.2
  change (∑ v, c v*x v) = PartialOptimum.number G R c at he
  rw [he] at hb
  exact ⟨D, hD, hb⟩

theorem certificate_optimum (a : ℝ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) (q : ℕ) :
    ∃ m : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ closed G r, m v) ∧
      (∑ v, c v*(m v : ℝ)) ≤ (q+2*(Nat.ceil a : ℝ))*PartialOptimum.number G R c := by
  let p := Nat.ceil a
  have hpa : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by exact_mod_cast (ha.trans hpa)
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G R c hc
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density G (MinorDensity.induced_bound G hden) p hpa
  obtain ⟨m, hm, hb⟩ := WeightedCertificate.exists_certificate G R O hp q c x hx.1 hx.2
  change (∑ v, c v*x v) = PartialOptimum.number G R c at he
  rw [he] at hb
  exact ⟨m, hm, hb⟩

theorem simultaneous_forest {T d κ μ : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d)
    (hdeg : G.IsKDegenerate d)
    (R : Fin (T + 1) → Finset V) (C : Fin T → Finset V)
    (hf : ∀ i v, v ∈ R i.succ → d + (T + T) * d * κ ≤ ((G.neighborFinset v) ∩ C i).card)
    (hh : ∀ i v, v ∈ C i → d + (T + T) * d * μ ≤ ((G.neighborFinset v) ∩ R i.castSucc).card) :
    Nonempty (Model G T κ μ R C) := by
  classical
  let A : Fin (T + T) → V → Finset V := Fin.append
    (fun i v => (G.neighborFinset v) ∩ C i)
    (fun i v => (G.neighborFinset v) ∩ R i.castSucc)
  let k : Fin (T + T) → V → ℕ := Fin.append
    (fun i v => if v ∈ R i.succ then κ else 0)
    (fun i v => if v ∈ C i then μ else 0)
  have hedge : ∀ j v u, u ∈ A j v → G.Adj v u := by
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro i v u hu
    · exact (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp (by simpa only [A, Fin.append_left, Fin.append_right] using hu)).1
    · exact (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp (by simpa only [A, Fin.append_left, Fin.append_right] using hu)).1
  have hrow : ∀ j v, 0 < k j v → d + ((T + T) * d) * k j v ≤ (A j v).card := by
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro i v hk
    · by_cases hv : v ∈ R i.succ
      · simpa only [A, k, Fin.append_left, Fin.append_right, if_pos hv] using hf i v hv
      · simp only [k, Fin.append_left, Fin.append_right, if_neg hv, lt_self_iff_false] at hk
    · by_cases hv : v ∈ C i
      · simpa only [A, k, Fin.append_left, Fin.append_right, if_pos hv] using hh i v hv
      · simp only [k, Fin.append_left, Fin.append_right, if_neg hv, lt_self_iff_false] at hk
  obtain ⟨O⟩ := SparseOrder.exists_of_degenerate G d hdeg
  obtain ⟨M⟩ := SimultaneousForest.exists_model G O hd (by omega) A k hedge hrow
  refine ⟨{
    rank := O.rank
    parent := M.parent
    decrease := M.decrease
    subgraph := M.subgraph
    demand_children := ?_
    candidate_children := ?_ }⟩
  · intro i v hv
    have hc := M.requirement_card (i.castAdd T, v)
    have hs : ((SimultaneousForest.eligible G O A (i.castAdd T) v).filter
        (fun u => M.parent u = some v)) ⊆
        (((G.neighborFinset v) ∩ C i).filter (fun u => M.parent u = some v)) := by
      intro u hu
      have hm := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by simpa only [A, Fin.append_left, Fin.append_right] using (Finset.mem_filter.mp hm.1).1, hm.2⟩
    have hc' : κ ≤ ((SimultaneousForest.eligible G O A (i.castAdd T) v).filter
        (fun u => M.parent u = some v)).card := by
      simpa only [k, Fin.append_left, if_pos hv] using hc
    exact hc'.trans (Finset.card_le_card hs)
  · intro i v hv
    have hc := M.requirement_card (i.natAdd T, v)
    have hs : ((SimultaneousForest.eligible G O A (i.natAdd T) v).filter
        (fun u => M.parent u = some v)) ⊆
        (((G.neighborFinset v) ∩ R i.castSucc).filter (fun u => M.parent u = some v)) := by
      intro u hu
      have hm := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by simpa only [A, Fin.append_left, Fin.append_right] using (Finset.mem_filter.mp hm.1).1, hm.2⟩
    have hc' : μ ≤ ((SimultaneousForest.eligible G O A (i.natAdd T) v).filter
        (fun u => M.parent u = some v)).card := by
      simpa only [k, Fin.append_right, if_pos hv] using hc
    exact hc'.trans (Finset.card_le_card hs)
end Paper.HumanDependencies
