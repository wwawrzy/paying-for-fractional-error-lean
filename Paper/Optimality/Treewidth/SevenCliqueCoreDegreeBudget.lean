import Paper.Optimality.Treewidth.SevenCliqueGlobalReduction
namespace Paper.SevenCliqueCoreDegreeBudget
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- Degree-eight and high-degree classes in the actual affine extremal core. -/
theorem balance (hmin : ∀ x, 8 ≤ G.degree x)
    (he : G.edgeFinset.card+14 = 5*Fintype.card V) :
    28 + 3*(Finset.univ.filter (fun x => 12 ≤ G.degree x)).card ≤
      Fintype.card V + (Finset.univ.filter (fun x => G.degree x = 8)).card := by
  have hp : ∀ x : V,
      9 + 3*(if 12 ≤ G.degree x then 1 else 0) ≤
        G.degree x + (if G.degree x = 8 then 1 else 0) := by
    intro x
    have hm := hmin x
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun x (_hx : x ∈ (Finset.univ : Finset V)) => hp x)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,Finset.sum_boole] at hs
  ring_nf at hs ⊢
  have hg := G.sum_degrees_eq_twice_card_edges
  norm_cast at hs
  omega
end Paper.SevenCliqueCoreDegreeBudget
