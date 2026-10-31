import Paper.Preliminaries.ExcludedCliqueHaven

/-! Exact s^(3/2)*sqrt(n) weighted excluded-clique separator. Integer sqrt
rounding costs no additive term: the sharper (s-2)n exchange budget pays
for taking floor sqrt(s*n), when n>=s. Small graphs are deleted outright. -/
namespace Paper.SharpExcludedSeparator
attribute [local instance] Classical.propDecidable
open WeightedHaven DeletionComponents HeavyComponent
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem radius_bounds (h n : ℕ) (hh : 1 ≤ h) (hn : h ≤ n) :
    1 ≤ Nat.sqrt (h*n) ∧ (h-2)*n ≤ Nat.sqrt (h*n)*Nat.sqrt (h*n) := by
  let r := Nat.sqrt (h*n)
  have hs := Nat.sqrt_le (h*n)
  have hadd := Nat.sqrt_le_add (h*n)
  have hr : r ≤ n := by dsimp [r]; nlinarith
  have hp : 0 < h*n := Nat.mul_pos (by omega) (by omega)
  have hrpos : 0 < r := Nat.sqrt_pos.mpr hp
  refine ⟨by omega, ?_⟩
  by_cases hh2 : 2 ≤ h
  · have he : (h-2)*n+2*n = h*n := by
      have hh' := Nat.sub_add_cancel hh2
      nlinarith
    dsimp [r] at hr
    nlinarith
  · have he : h-2 = 0 := by omega
    simp only [he, zero_mul, zero_le]

theorem sqrt_bound (h : ℕ) (hh : 1 ≤ h) (hfree : G.IsKMinorFree h)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ X : Finset V, (X.card : ℝ) ≤ ((h : ℝ)*Real.sqrt h)*Real.sqrt (Fintype.card V) ∧
      ∀ C : (deleted G X).ConnectedComponent, mass w (physical G X C) ≤ (∑ v, w v)/2 := by
  let n := Fintype.card V
  by_cases hn : h ≤ n
  · have hb := radius_bounds h n hh hn
    obtain ⟨X, hX, hbal⟩ := ExcludedCliqueHaven.balanced G h hfree (Nat.sqrt (h*n)) hb.1 hb.2 w hw
    refine ⟨X, ?_, hbal⟩
    have hr : ((Nat.sqrt (h*n) : ℕ) : ℝ) ≤ Real.sqrt h*Real.sqrt n := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg h)]
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast Nat.sqrt_le' (h*n)
    have hX' : (X.card : ℝ) ≤ (h : ℝ)*(Nat.sqrt (h*n) : ℕ) := by exact_mod_cast hX
    exact hX'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg h))
  · refine ⟨Finset.univ, ?_, ?_⟩
    · rw [Finset.card_univ]
      change (n : ℝ) ≤ ((h : ℝ)*Real.sqrt h)*Real.sqrt n
      by_cases hn0 : n = 0
      · simp [hn0]
      have hn1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n))
      have hh1 : (1 : ℝ) ≤ Real.sqrt h := Real.one_le_sqrt.mpr (by exact_mod_cast hh)
      calc
        (n : ℝ) ≤ h := by exact_mod_cast (show n ≤ h by omega)
        _ = ((h : ℝ)*1)*1 := by ring
        _ ≤ _ := by gcongr
    · intro C
      obtain ⟨v, hv⟩ := DeletionComponents.nonempty G Finset.univ C
      have had := DeletionComponents.avoids G Finset.univ C
      exact False.elim (Finset.disjoint_left.mp had hv (Finset.mem_univ v))

theorem coefficient_eq (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ)*Real.sqrt h = (h : ℝ)^(3/2 : ℝ) := by
  have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rw [show (3/2 : ℝ) = 1+1/2 by ring, Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem published_bound (h : ℕ) (hh : 1 ≤ h) (hfree : G.IsKMinorFree h)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ X : Finset V, (X.card : ℝ) ≤ (h : ℝ)^(3/2 : ℝ)*Real.sqrt (Fintype.card V) ∧
      ∀ C : (deleted G X).ConnectedComponent, mass w (physical G X C) ≤ 2*(∑ v, w v)/3 := by
  obtain ⟨X, hX, hbal⟩ := sqrt_bound G h hh hfree w hw
  refine ⟨X, by simpa only [coefficient_eq h hh] using hX, ?_⟩
  intro C
  have hnonneg : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => hw v)
  have hb := hbal C
  linarith

/-- The minor-density hypothesis excludes the exact clique used by the source. -/
theorem excludes_clique {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (h : ℕ) (hh : 2*a+1 < h) : G.IsKMinorFree h := by
  rintro ⟨M⟩
  let J := SimpleGraph.completeGraph (Fin h)
  have hd := hden (Fin h) J ⟨M⟩
  have hhp : 0 < h := by
    have hp : (0 : ℝ) < h := by linarith
    exact_mod_cast hp
  have he : (h-1)*h = 2*J.edgeFinset.card := by
    have hs := SimpleGraph.sum_degrees_eq_twice_card_edges J
    simpa only [J, SimpleGraph.complete_graph_degree, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] using hs
  have he' : ((h : ℝ)-1)*h = 2*(J.edgeFinset.card : ℝ) := by
    have hs := congrArg (fun n : ℕ => (n : ℝ)) he
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ h by omega), Nat.cast_one, Nat.cast_ofNat] using hs
  simp only [Fintype.card_fin] at hd
  have hp : (0 : ℝ) < h := by exact_mod_cast hhp
  nlinarith

end Paper.SharpExcludedSeparator
