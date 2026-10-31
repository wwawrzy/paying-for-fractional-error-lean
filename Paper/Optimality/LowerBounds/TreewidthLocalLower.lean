import Paper.Solver.LocalSearch.IntegralFractionalOptima
import Paper.Optimality.LowerBounds.PortLocalCompiler
import Paper.Optimality.LowerBounds.PathPowerLocalLower

namespace Paper.TreewidthLocalLower
open PathPowerTreewidth SevenFoundation

def output {n : ℕ} (N : PortLocal.Network (Fin n)) (P : PortLocal.Program Unit Bool)
    (ids : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => P.run N ids (fun _ => ()) v = true)

/-- No fixed-round deterministic LOCAL algorithm achieves factor c<2t+1,
even if its code knows exact n and all neighbor IDs initially (KT1).
All ports are ordinary consecutive numbers. The witness graph is an actual
finite simple graph of treewidth<=t; the IDs are distinct and at most n.
The finite size n is selected before the algorithm's code. -/
theorem lower (t T : ℕ) (c : ℝ) (hc : 0 ≤ c) (hct : c < 2*t+1) :
    ∃ n : ℕ, 0 < n ∧ (graph n t).treeWidth ≤ t ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n t) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n t) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n t) ∧ Function.Injective ids ∧
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
          c * (graph n t).dominationNumber < (output N P ids).card := by
  obtain ⟨n, hn, htw, hbad⟩ := PathPowerLocalLower.lower t T c hc hct
  refine ⟨n, hn, htw, ?_⟩
  intro P hP hdom
  have he (ids : Fin n → ℕ) :
      Finset.univ.filter (fun v => LineLocalWindow.output (PortLocalCompiler.translate t P) ids v = true) =
        output (PortLocalCompiler.network (t := t) ids) P ids := by
    ext v
    simp only [output, Finset.mem_filter, Finset.mem_univ, true_and, LineLocalWindow.output]
    rw [PortLocalCompiler.translate_correct P ids (fun _ => ()) (fun _ => ()) (fun _ => rfl)]
  obtain ⟨ids, hinj, hIDs, hsize⟩ := hbad (PortLocalCompiler.translate t P)
    (by simpa only [PortLocalCompiler.rounds] using hP) (by
      intro ids hinj hIDs
      rw [he]
      exact hdom _ (PortLocalCompiler.compatible ids) ids hinj hIDs)
  exact ⟨PortLocalCompiler.network ids, ids, PortLocalCompiler.compatible ids, hinj, hIDs,
    by simpa only [he] using hsize⟩

theorem exact_identifiers {n : ℕ} (ids : Fin n → ℕ) (hinj : Function.Injective ids)
    (hIDs : ∀ i, 1 ≤ ids i ∧ ids i ≤ n) :
    Finset.univ.image ids = Finset.Icc 1 n := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (hIDs i)
  · rw [Finset.card_image_of_injective _ hinj]
    simp

/-- Full quantifier c<2t+1, without imposing c>=0. -/
theorem exact_lower (t T : ℕ) (c : ℝ) (hct : c < 2*t+1) :
    ∃ n : ℕ, 0 < n ∧ (graph n t).treeWidth ≤ t ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n t) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n t) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n t) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c * (graph n t).dominationNumber < (output N P ids).card := by
  have hmax : max c 0 < 2*t+1 := max_lt hct (by positivity)
  obtain ⟨n, hn, htw, hbad⟩ := lower t T (max c 0) (le_max_right _ _) hmax
  refine ⟨n, hn, htw, ?_⟩
  intro P hP hdom
  obtain ⟨N, ids, hN, hinj, hIDs, hsize⟩ := hbad P hP hdom
  refine ⟨N, ids, hN, hinj, exact_identifiers ids hinj hIDs, ?_⟩
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg _)).trans_lt hsize

/-- The same lower bound holds against the fractional benchmark. -/
theorem fractional_lower (t T : ℕ) (c : ℝ) (hct : c < 2*t+1) :
    ∃ n : ℕ, 0 < n ∧ (graph n t).treeWidth ≤ t ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n t) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates (graph n t) (output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n t) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c * fractionalNumber (graph n t) < (output N P ids).card := by
  have hmax : max c 0 < 2*t+1 := max_lt hct (by positivity)
  obtain ⟨n, hn, htw, hbad⟩ := exact_lower t T (max c 0) hmax
  refine ⟨n, hn, htw, ?_⟩
  intro P hP hdom
  obtain ⟨N, ids, hN, hinj, hIDs, hsize⟩ := hbad P hP hdom
  refine ⟨N, ids, hN, hinj, hIDs, ?_⟩
  calc
    c * fractionalNumber (graph n t) ≤ max c 0 * fractionalNumber (graph n t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (IntegralFractionalOptima.fractional_nonneg _)
    _ ≤ max c 0 * (graph n t).dominationNumber :=
      mul_le_mul_of_nonneg_left (IntegralFractionalOptima.fractional_le_domination _) (le_max_right _ _)
    _ < _ := hsize

end Paper.TreewidthLocalLower
