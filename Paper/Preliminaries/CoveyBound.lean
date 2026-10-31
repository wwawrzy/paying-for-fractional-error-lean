import Paper.Preliminaries.Covey

/-! The physical all-minors density bound excludes large actual coveys. -/
namespace Paper.CoveyBound
attribute [local instance] Classical.propDecidable
open Covey
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_lt {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (s : ℕ) (hs : 2 * a + 1 < s) {C : Finset (Finset V)} (hC : IsCovey G C) : C.card < s := by
  classical
  by_contra hn
  have hcs : s ≤ C.card := by omega
  have hsp : (0 : ℝ) < s := by linarith
  have hsn : 0 < s := by exact_mod_cast hsp
  have hcp : 1 ≤ C.card := by omega
  let J : SimpleGraph C := ⊤
  have hd := hden C J ⟨Covey.model G hC⟩
  rw [Fintype.card_coe] at hd
  have he : (C.card - 1) * C.card = 2 * J.edgeFinset.card := by
    have hh := SimpleGraph.sum_degrees_eq_twice_card_edges J
    simpa only [J, SimpleGraph.complete_graph_degree, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul, mul_comm] using hh
  have he' : ((C.card : ℝ) - 1) * C.card = 2 * (J.edgeFinset.card : ℝ) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) he
    simpa only [Nat.cast_mul, Nat.cast_sub hcp, Nat.cast_one, Nat.cast_ofNat] using hh
  have hcsp : (s : ℝ) ≤ C.card := by exact_mod_cast hcs
  have hcpos : (0 : ℝ) < C.card := by exact_mod_cast (show 0 < C.card by omega)
  have hp := mul_pos (by linarith : 0 < (C.card : ℝ) - 1 - 2 * a) hcpos
  nlinarith
end Paper.CoveyBound
