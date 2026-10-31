import Paper.TotalDomination.HighGirthSetup
import Paper.TotalDomination.HighGirthSavingArithmetic

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem saving (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hsupport : ∀ v ∉ K G, x v = 0) :
    0 ≤ penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) ∧
    0 ≤ oversupply G (I G x identifier hfree) ∧
    (first G (I G x identifier hfree)).card / 3 +
      ((9-8*a)/(3*(3-2*a)))*surplus G (I G x identifier hfree) +
      (linkedLast G x identifier hfree).card +
      penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) +
      oversupply G (I G x identifier hfree) ≤
      objective G (I G x identifier hfree) (fun v => (c G v : ℝ)) -
      (selected G x identifier hfree).card := by
  classical
  have hR1 : ∀ v ∈ first G (I G x identifier hfree) ∪ high G (I G x identifier hfree),
      (c G v : ℝ) = 2*(1:ℝ) := by
    intro v hv
    have he := full_cost G x identifier hfree hv
    exact_mod_cast he
  have hpen := penalty_nonneg G (I G x identifier hfree) (fun v => (c G v : ℝ))
    (fun v _ => hx.1 v) (fun v hv => by
      change (hits G (I G x identifier hfree) v : ℝ) ≤ (c G v : ℝ)
      exact_mod_cast other_hits_cost G x identifier hfree hv)
  have homega := oversupply_nonneg G (I G x identifier hfree) (fun r hr => hx.2 r hr)
  have hcost := cost_decomposition G (I G x identifier hfree) 1
    (fun v => (c G v : ℝ)) hsupport hR1
  simp only [show (I G x identifier hfree).x = x from rfl] at hcost
  have hweighted := weighted_excess_le G (I G x identifier hfree) 1
    (by change 2*(1:ℝ) ≤ (3:ℝ); norm_num)
    (fun v hv _ => high_weight G x identifier hfree hv)
  have hfirst : (2/3:ℝ)*(first G (I G x identifier hfree)).card ≤
      ∑ v ∈ first G (I G x identifier hfree), x v := by
    calc
      _ = ∑ _v ∈ first G (I G x identifier hfree), (2/3:ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2.le
  have hcount := selected_card_le G x identifier hfree
  obtain ⟨_,_,_,hE⟩ := HighGirthSavingArithmetic.density_counts G (I G x identifier hfree) a ha hhi hden rfl
  have hd : 3-2*a ≠ 0 := by linarith
  have hpay : (2/3:ℝ)*(a*surplus G (I G x identifier hfree)/(3-2*a)) +
      ((9-8*a)/(3*(3-2*a)))*surplus G (I G x identifier hfree) =
      surplus G (I G x identifier hfree) := by
    field_simp
    <;> ring
  have hEscaled := mul_le_mul_of_nonneg_left hE (show (0:ℝ) ≤ 2/3 by norm_num)
  change (∑ v ∈ high G (I G x identifier hfree), ((hits G (I G x identifier hfree) v : ℝ)-2*1)*x v) ≤
    (2/3:ℝ)*excess G (I G x identifier hfree) 1 at hweighted
  refine ⟨hpen,homega,?_⟩
  simp only [mul_one] at hcost hweighted
  have hlower : (4/3:ℝ)*(first G (I G x identifier hfree)).card +
      (residual G (I G x identifier hfree)).card +
      oversupply G (I G x identifier hfree) + penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) -
      (2/3:ℝ)*excess G (I G x identifier hfree) 1 ≤
      objective G (I G x identifier hfree) (fun v => (c G v : ℝ)) := by
    linarith only [hcost,hweighted,hfirst]
  have hpaid : ((9-8*a)/(3*(3-2*a)))*surplus G (I G x identifier hfree) ≤
      surplus G (I G x identifier hfree) - (2/3:ℝ)*excess G (I G x identifier hfree) 1 := by
    linarith only [hEscaled,hpay]
  linarith only [hlower,hpaid,hcount]

/-- Full fv:hg:t-saving, for the actual branch threshold and linked-demand rule. -/
theorem rounding_saving (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hsupport : ∀ v ∉ K G, x v = 0) :
    (∀ r, ∃ v ∈ F G ∪ selected G x identifier hfree, G.Adj r v) ∧
    0 ≤ surplus G (I G x identifier hfree) ∧
    ((high G (I G x identifier hfree)).card : ℝ) ≤ a*surplus G (I G x identifier hfree)/(3-2*a) ∧
    ((served G (I G x identifier hfree)).card : ℝ) ≤ (3-a)*surplus G (I G x identifier hfree)/(3-2*a) ∧
    0 < (9-8*a)/(3*(3-2*a)) ∧
    (first G (I G x identifier hfree)).card / 3 +
      ((9-8*a)/(3*(3-2*a)))*surplus G (I G x identifier hfree) +
      (linkedLast G x identifier hfree).card +
      penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) +
      oversupply G (I G x identifier hfree) ≤
      objective G (I G x identifier hfree) (fun v => (c G v : ℝ)) -
      (selected G x identifier hfree).card := by
  obtain ⟨hj,hH,hY,_⟩ := HighGirthSavingArithmetic.density_counts G (I G x identifier hfree) a ha hhi hden rfl
  exact ⟨total_dominates G x identifier hfree,hj,hH,hY,
    HighGirthSavingArithmetic.beta_pos a hhi,(saving G x identifier hfree a ha hhi hden hx hsupport).2.2⟩

end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.saving

#print axioms Paper.TotalDomination.HighGirthSetup.rounding_saving
