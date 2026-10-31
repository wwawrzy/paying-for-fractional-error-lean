import Paper.Preliminaries.MinorDensity

/-! A genuine sparse acyclic order from the real induced-density bound. -/
namespace Paper.SparseOrder
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Model (d : ℕ) where
  rank : V → ℕ
  injective : Function.Injective rank
  bound : ∀ v, (Finset.univ.filter (fun u => rank u < rank v ∧ G.Adj v u)).card ≤ d

theorem exists_of_degenerate (d : ℕ) (hG : G.IsKDegenerate d) : Nonempty (Model G d) := by
  classical
  obtain ⟨ord, hnd, hmem, hbnd⟩ := G.exists_degeneracy_order hG
  let e := hnd.getEquivOfForallMemList ord hmem
  refine ⟨⟨fun v => (e.symm v).val, ?_, ?_⟩⟩
  · intro u v h
    exact e.symm.injective (Fin.ext h)
  · intro v
    apply le_trans _ (hbnd (e.symm v))
    apply Finset.card_le_card_of_injOn e.symm
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hu'.1, ?_⟩
      have hv_eq : ord.get (e.symm v) = v := by
        have h := e.apply_symm_apply v
        rwa [List.Nodup.getEquivOfForallMemList_apply] at h
      have hu_eq : ord.get (e.symm u) = u := by
        have h := e.apply_symm_apply u
        rwa [List.Nodup.getEquivOfForallMemList_apply] at h
      rw [hv_eq, hu_eq]
      exact hu'.2
    · intro u _ w _ h
      exact e.symm.injective h

theorem exists_of_density (d : ℕ) {t : ℝ} (hden : Incidence.InducedDensityBound G t)
    (hdt : 2 * t ≤ d) : Nonempty (Model G d) := by
  apply exists_of_degenerate G d
  intro S hS
  by_contra hn
  push Not at hn
  have hl : (d + 1) * S.card ≤ ∑ v ∈ S, G.inducedDegree v S := by
    calc
      _ = ∑ _v ∈ S, (d + 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => by have h := hn v hv; omega)
  rw [InducedCounting.sum_inducedDegree_eq_two_mul] at hl
  have hl' : ((d : ℝ) + 1) * S.card ≤ 2 * (G.inducedEdgeCount S : ℝ) := by exact_mod_cast hl
  have hc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hu := hden S
  have hd := mul_le_mul_of_nonneg_right hdt hc.le
  nlinarith
end Paper.SparseOrder
