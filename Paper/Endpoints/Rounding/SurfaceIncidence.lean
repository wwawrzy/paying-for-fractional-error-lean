import Paper.Endpoints.Rounding.CurrentCountBound
namespace Paper.SurfaceRounding
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem closed_incidence_additive (a η : ℝ)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S:ℝ) ≤ a*S.card+η) (A B : Finset V) :
    (∑ v ∈ A, ((closed G v ∩ B).card:ℝ)) ≤
      a*(A ∪ B).card+(a+1)*(A ∩ B).card+2*η := by
  have hn := Incidence.closed_incidence_le G A B
  have hr : (∑ v ∈ A, ((closed G v ∩ B).card:ℝ)) ≤
      (G.inducedEdgeCount (A ∪ B):ℝ)+(G.inducedEdgeCount (A ∩ B):ℝ)+(A ∩ B).card := by exact_mod_cast hn
  linarith [hden (A ∪ B),hden (A ∩ B)]
variable (a : ℝ) (I : CurrentRounding.Input G a)
theorem excess_additive (η : ℝ) (hden : ∀ S : Finset V, (G.inducedEdgeCount S:ℝ) ≤ a*S.card+η) :
    CurrentRounding.excess G a I + (a + 1) * (CurrentRounding.outside G a I).card ≤ a * (CurrentRounding.middle G a I).card+2*η := by
  classical
  have hinc := closed_incidence_additive G a η hden
    (CurrentRounding.high G a I) (CurrentRounding.residual G a I ∩ covered G (CurrentRounding.high G a I))
  have hsum : (∑ v ∈ CurrentRounding.high G a I,
      ((closed G v ∩ (CurrentRounding.residual G a I ∩ covered G (CurrentRounding.high G a I))).card : ℝ)) =
      ∑ v ∈ CurrentRounding.high G a I, (CurrentRounding.hits G a I v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have he : closed G v ∩ (CurrentRounding.residual G a I ∩ covered G (CurrentRounding.high G a I)) =
        closed G v ∩ CurrentRounding.residual G a I := by
      ext r
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hc, hr, _⟩
        exact ⟨hc, hr⟩
      · rintro ⟨hc, hr⟩
        exact ⟨hc, hr, Finset.mem_biUnion.mpr ⟨v, hv, hc⟩⟩
    rw [he]
    rfl
  rw [hsum, CurrentRounding.covered_inter_high, CurrentRounding.covered_union_high,
    Finset.card_union_of_disjoint (CurrentRounding.high_middle_disjoint G a I)] at hinc
  have hcard : ((CurrentRounding.high G a I).card : ℝ) =
      (CurrentRounding.overlap G a I).card + (CurrentRounding.outside G a I).card := by
    exact_mod_cast CurrentRounding.high_card_split G a I
  have he : CurrentRounding.excess G a I = (∑ v ∈ CurrentRounding.high G a I, (CurrentRounding.hits G a I v : ℝ)) -
      (2 * a + 1) * (CurrentRounding.high G a I).card := by
    simp [CurrentRounding.excess, Finset.sum_sub_distrib, mul_comm]
    ring
  push_cast at hinc
  rw [hcard] at he hinc
  rw [he]
  nlinarith

end Paper.SurfaceRounding
#print axioms Paper.SurfaceRounding.excess_additive
