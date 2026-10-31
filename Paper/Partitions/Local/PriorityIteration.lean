import Paper.Partitions.Local.PriorityStage
import Paper.Preliminaries.FiniteIteration

/-! The actual finite local priority iteration leaves a geometrically small
mean residual. Every stage uses fresh independent finite priorities. -/
namespace Paper.PriorityIteration
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def rate (Q : ℕ) : ℝ := 1 - 1 / (4 * Q)

theorem rate_bounds (Q : ℕ) (hQ : 0 < Q) : 0 ≤ rate Q ∧ rate Q < 1 := by
  have hpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  unfold rate
  constructor
  · have h := (div_le_one (by positivity : (0 : ℝ) < 4 * Q)).mpr (by linarith : (1 : ℝ) ≤ 4 * Q)
    linarith
  · have h : (0 : ℝ) < 1 / (4 * Q) := by positivity
    linarith

theorem mean_step {C ε : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (hε : 0 < ε)
    (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε)
    (Q : ℕ) (hQ : 0 < Q) (hsize : 2 * (k * 2 ^ ((Δ + 1) ^ k)) ≤ Q) (S : Finset V) :
    (∑ ω : Finset V → Fin Q, ((PriorityStage.next G S k ε ω).card : ℝ)) ≤
      rate Q * Fintype.card (Finset V → Fin Q) * S.card := by
  have hb := PriorityStage.remaining_bound G hC hprofile Δ hdeg k hk hε hparam Q hQ hsize S
  have hsub : 1 ≤ 4 * Q := by omega
  have hr : (4 * Q : ℝ) * (∑ ω : Finset V → Fin Q, ((PriorityStage.next G S k ε ω).card : ℝ)) ≤
      (4 * Q - 1 : ℝ) * Fintype.card (Finset V → Fin Q) * S.card := by exact_mod_cast hb
  have hpos : (0 : ℝ) < 4 * Q := by exact_mod_cast (show 0 < 4 * Q by omega)
  have he : rate Q * (4 * Q) = 4 * Q - 1 := by unfold rate; field_simp
  have he' := congrArg (fun x : ℝ => x * Fintype.card (Finset V → Fin Q) * S.card) he
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith

theorem remaining {C ε : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (hε : 0 < ε)
    (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε)
    (Q : ℕ) (hQ : 0 < Q) (hsize : 2 * (k * 2 ^ ((Δ + 1) ^ k)) ≤ Q) (n : ℕ) (S : Finset V) :
    (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      ((FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card : ℝ)) ≤
      rate Q ^ n * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card :=
  FiniteIteration.geometric _ (fun T => (T.card : ℝ)) (rate Q) (rate_bounds Q hQ).1
    (mean_step G hC hprofile Δ hdeg k hk hε hparam Q hQ hsize) n S

theorem exists_stages (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, rate Q ^ n ≤ δ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (rate_bounds Q hQ).2
  exact ⟨n, hn.le⟩
end Paper.PriorityIteration
