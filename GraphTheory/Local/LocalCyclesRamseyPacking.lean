import GraphTheory.Local.LocalCyclesRamseyReservoir
import GraphTheory.Local.LocalCyclesCriticalBridge

/-! Repeated homogeneous-block extraction and the exact finite cost margin.
Every block is a subset of the same original identifier set. -/

noncomputable section

namespace LocalCyclesRamseyPacking

open LocalCyclesRamseyReservoir LocalCyclesCriticalBridge LocalCyclesReflection
open scoped BigOperators

theorem homogeneous_partition (q k L : ℕ) (hq : 0 < q) (hL : k+1 ≤ L)
    (f : Finset ℕ → Fin q) (U : Finset ℕ) :
    ∃ (blocks : Finset (Finset ℕ)) (leftover : Finset ℕ),
      (blocks : Set (Finset ℕ)).PairwiseDisjoint id ∧
      (∀ T ∈ blocks, T.card = L ∧ Homogeneous f (k+1) T) ∧
      blocks.biUnion id ∪ leftover = U ∧ Disjoint (blocks.biUnion id) leftover ∧
      U.card = blocks.card*L+leftover.card ∧ leftover.card < ramseyBound q k L := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hsmall : U.card < ramseyBound q k L
    · refine ⟨∅, U, ?_, by simp, by simp, by simp, by simp, hsmall⟩
      simp
    · obtain ⟨T, hTU, hTcard, hTmono⟩ :=
        quantitative_ramsey q k L hq hL f U (Nat.le_of_not_gt hsmall)
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨blocks, leftover, hdis, hblocks, hcover, hleftdis, hcount, hrest⟩ :=
        ih (U \ T) (Finset.sdiff_ssubset hTU hTne)
      have hunionSub : blocks.biUnion id ⊆ U \ T := by
        rw [← hcover]
        exact Finset.subset_union_left
      have hleftSub : leftover ⊆ U \ T := by
        rw [← hcover]
        exact Finset.subset_union_right
      have hTUdis : Disjoint T (U \ T) := by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        exact (Finset.mem_sdiff.mp hb).2 ha
      have hTB : ∀ B ∈ blocks, Disjoint T B := by
        intro B hB
        apply hTUdis.mono_right
        intro a ha
        exact hunionSub (Finset.mem_biUnion.mpr ⟨B, hB, ha⟩)
      have hTnot : T ∉ blocks := by
        intro hT
        have hempty : T = ∅ := by simpa using hTB T hT
        exact hTne.ne_empty hempty
      refine ⟨insert T blocks, leftover, ?_, ?_, ?_, ?_, ?_, hrest⟩
      · simp only [Finset.coe_insert]
        exact hdis.insert_of_notMem hTnot hTB
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact ⟨hTcard, hTmono⟩
        · exact hblocks B hB
      · rw [Finset.biUnion_insert, id_eq, Finset.union_assoc, hcover]
        exact Finset.union_sdiff_of_subset hTU
      · rw [Finset.biUnion_insert, id_eq]
        exact Finset.disjoint_union_left.mpr ⟨hTUdis.mono_right hleftSub, hleftdis⟩
      · rw [Finset.card_insert_of_notMem hTnot]
        have hcard := Finset.card_sdiff_add_card_eq_card hTU
        rw [hTcard, hcount] at hcard
        nlinarith

/-- The packing ledger keeps the leftover loss and the loss at every block
boundary explicit. No asymptotic O(1) term is discarded. -/
theorem block_loop_budget (n blocks L rest s : ℕ) (hsize : n = blocks*L+rest)
    (hs : s ≤ L) :
    blocks*(L-s)+rest+blocks*s = n := by
  have hsub : L-s+s = L := Nat.sub_add_cancel hs
  nlinarith

/-- A finite set of actual loops at density at least 1-ρ yields the exact
weighted lower bound. Costs of every exceptional transition are nonnegative. -/
theorem run_cost_lower_of_loops {n : ℕ} [NeZero n] {Q : Type*}
    (c : Q → Q → ℝ) (states : Fin n → Q) (loops : Finset (Fin n)) (B Δ : ℝ)
    (hcost : ∀ i, 0 ≤ c (states i) (states (right i 1)))
    (hloops : ∀ i ∈ loops,
      states i = states (right i 1) ∧ B+Δ ≤ c (states i) (states i)) :
    (B+Δ)*loops.card ≤ runCost c states := by
  calc
    (B+Δ)*loops.card = ∑ _i ∈ loops, (B+Δ) := by simp [mul_comm]; ring
    _ ≤ ∑ i ∈ loops, c (states i) (states (right i 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨he, hc⟩ := hloops i hi
      simpa only [← he] using hc
    _ ≤ ∑ i, c (states i) (states (right i 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hcost i)
    _ = runCost c states := rfl

/-- The positive finite loop-cost gap gives a strict contradiction, including
an explicit Δn/2 margin, once at most Δn/(2(B+Δ)) transitions are exceptional. -/
theorem strict_cost_of_dense_expensive_loops {n : ℕ} [NeZero n] {Q : Type*}
    (c : Q → Q → ℝ) (states : Fin n → Q) (loops : Finset (Fin n)) (B Δ : ℝ)
    (hB : 0 ≤ B) (hΔ : 0 < Δ)
    (hcost : ∀ i, 0 ≤ c (states i) (states (right i 1)))
    (hloops : ∀ i ∈ loops,
      states i = states (right i 1) ∧ B+Δ ≤ c (states i) (states i))
    (hdense : (n : ℝ)-loops.card ≤ Δ*n/(2*(B+Δ))) :
    B*n < runCost c states := by
  have hpos : 0 < B+Δ := by linarith
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hd := (le_div_iff₀ (show 0 < 2*(B+Δ) by positivity)).mp hdense
  have hlower := run_cost_lower_of_loops c states loops B Δ hcost hloops
  nlinarith

/-- Two explicit numerical cutoffs control the leftover and block seams.
This lemma avoids square-root rounding and retains all integer losses. -/
theorem dense_count_from_cutoffs (n blocks rest loops r C H : ℕ) (ρ : ℝ)
    (hn : 0 < n) (hρ : 0 < ρ)
    (hsize : n = blocks*(C*(r+1))+rest)
    (hloops : loops+rest+blocks*(2*r+1) = n)
    (hrest : rest ≤ H) (hH : (H : ℝ)^2 ≤ n)
    (hcut : 1/ρ^2 ≤ n) (hC : 2 ≤ ρ*C) :
    (n : ℝ)-loops ≤ 2*ρ*n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ2 : 0 < ρ^2 := sq_pos_of_pos hρ
  have hmul : 1 ≤ (n : ℝ)*ρ^2 := (div_le_iff₀ hρ2).mp hcut
  have hmuln := mul_le_mul_of_nonneg_right hmul hn'.le
  have hHnonneg : (0 : ℝ) ≤ H := by positivity
  have hρn : 0 ≤ ρ*n := by positivity
  have hsmall : (H : ℝ) ≤ ρ*n := by nlinarith
  have hrest' : (rest : ℝ) ≤ ρ*n :=
    (show (rest : ℝ) ≤ H by exact_mod_cast hrest).trans hsmall
  have hsize' : (n : ℝ) = blocks*(C*((r : ℝ)+1))+rest := by exact_mod_cast hsize
  have hloops' : (loops : ℝ)+rest+blocks*(2*(r : ℝ)+1) = n := by exact_mod_cast hloops
  have hbnonneg : (0 : ℝ) ≤ blocks := by positivity
  have hbR : 0 ≤ (blocks : ℝ)*((r : ℝ)+1) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hC hbR
  have hnB : (blocks : ℝ)*(C*((r : ℝ)+1)) ≤ n := by
    nlinarith [show (0 : ℝ) ≤ rest by positivity]
  have hnρ := mul_le_mul_of_nonneg_left hnB hρ.le
  have hseams : (blocks : ℝ)*(2*(r : ℝ)+1) ≤ ρ*n := by nlinarith
  nlinarith

/-- A successful run with the proved density has a cheap loop among its
actual transitions. A uniform positive gap is needed only above B. -/
theorem exists_cheap_used_loop {n : ℕ} [NeZero n] {Q : Type*}
    (c : Q → Q → ℝ) (states : Fin n → Q) (loops : Finset (Fin n)) (B Δ : ℝ)
    (hB : 0 ≤ B) (hΔ : 0 < Δ)
    (hcost : ∀ i, 0 ≤ c (states i) (states (right i 1)))
    (hloops : ∀ i ∈ loops, states i = states (right i 1))
    (hgap : ∀ q, B < c q q → B+Δ ≤ c q q)
    (hdense : (n : ℝ)-loops.card ≤ Δ*n/(2*(B+Δ)))
    (hsuccess : runCost c states ≤ B*n) :
    ∃ i ∈ loops, c (states i) (states i) ≤ B := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict := strict_cost_of_dense_expensive_loops c states loops B Δ hB hΔ hcost
    (fun i hi => ⟨hloops i hi, hgap _ (hnone i hi)⟩) hdense
  linarith

/-- Every finite output alphabet has a uniform positive cost gap above B.
This remains true when no state has loop cost above B. -/
theorem exists_uniform_positive_gap {Q : Type*} [Fintype Q]
    (cost : Q → ℝ) (B : ℝ) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ q, B < cost q → B+Δ ≤ cost q := by
  classical
  suffices ∀ S : Finset Q, ∃ Δ : ℝ, 0 < Δ ∧ ∀ q ∈ S, B < cost q → B+Δ ≤ cost q by
    obtain ⟨Δ, hΔ, hbound⟩ := this Finset.univ
    exact ⟨Δ, hΔ, fun q => hbound q (Finset.mem_univ q)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert q S hq ih =>
    obtain ⟨Δ, hΔ, hbound⟩ := ih
    by_cases hcost : B < cost q
    · refine ⟨min Δ (cost q-B), lt_min hΔ (by linarith), ?_⟩
      intro x hx hxB
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have hh := min_le_right Δ (cost x-B)
        linarith
      · have hh := hbound x hx hxB
        have hmin := min_le_left Δ (cost q-B)
        linarith
    · refine ⟨Δ, hΔ, ?_⟩
      intro x hx hxB
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact False.elim (hcost hxB)
      · exact hbound x hx hxB

#print axioms homogeneous_partition
#print axioms strict_cost_of_dense_expensive_loops
#print axioms dense_count_from_cutoffs
#print axioms exists_cheap_used_loop
#print axioms exists_uniform_positive_gap

end LocalCyclesRamseyPacking
