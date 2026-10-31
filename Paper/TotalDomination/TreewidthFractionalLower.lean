import Paper.TotalDomination.PathPowerGap
import Paper.Optimality.LowerBounds.TreewidthLocalLower

/-! Actual standard-port LOCAL lower bound against the fractional total
benchmark on connected powers of paths. Exact size is selected before code. -/
namespace Paper.TotalDomination.TreewidthFractionalLower
open SevenFoundation PathPowerTreewidth

theorem connected (n t : ℕ) (hn : 0 < n) (ht : 1 ≤ t) : (graph n t).Connected := by
  have hsub : SimpleGraph.pathGraph n ≤ graph n t := by
    intro u v ha
    have hh := SimpleGraph.pathGraph_adj.mp ha
    refine ⟨ha.ne,?_,?_⟩ <;> rcases hh with hh | hh <;> omega
  exact SimpleGraph.Connected.mono hsub (PathGraphTree.tree n hn).connected

/-- The coefficient 2t cannot be decreased, even with exact n and exact IDs.
The t=1 strengthening to the integral total optimum is proved separately. -/
theorem lower (t T : ℕ) (ht : 1 ≤ t) (c : ℝ) (hct : c < 2*t) :
    ∃ n : ℕ, 2 ≤ n ∧ (graph n t).Connected ∧ (graph n t).treeWidth ≤ t ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n t) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (graph n t).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n t) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*FractionalSolver.fractionalNumber (graph n t) < (TreewidthLocalLower.output N P ids).card := by
  have hmax : max c 0 < 2*t := max_lt hct (by
    have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
    positivity)
  obtain ⟨n,hn,hwindow⟩ := PathPowerGap.window_lower_bound t (t*(T+1)) ht (max c 0) (le_max_right _ _) hmax
  refine ⟨n,hn,connected n t (by omega) ht,treeWidth_le n t,?_⟩
  intro P hP hdom
  have he (ids : Fin n → ℕ) :
      Finset.univ.filter (fun v => LineLocalWindow.output (PortLocalCompiler.translate t P) ids v = true) =
        TreewidthLocalLower.output (PortLocalCompiler.network (t := t) ids) P ids := by
    ext v
    simp only [TreewidthLocalLower.output,Finset.mem_filter,Finset.mem_univ,true_and,LineLocalWindow.output]
    rw [PortLocalCompiler.translate_correct P ids (fun _ => ()) (fun _ => ()) (fun _ => rfl)]
  obtain ⟨ids,hinj,hIDs,hbad⟩ := hwindow (LineLocalWindow.rule (PortLocalCompiler.translate t P) (t*(T+1)))
  have hagree := LineLocalWindow.agrees (PortLocalCompiler.translate t P) (t*(T+1))
    (by
      unfold LineLocal.Program.radius
      rw [PortLocalCompiler.rounds]
      nlinarith) ids
  have hclosed : dominates (graph n t) (Finset.univ.filter
      (fun v => LineLocalWindow.output (PortLocalCompiler.translate t P) ids v = true)) := by
    rw [he]
    intro r
    obtain ⟨v,hv,ha⟩ := hdom _ (PortLocalCompiler.compatible ids) ids hinj hIDs r
    exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_closed (graph n t) r v).mpr (Or.inr ha.symm)⟩
  have hsize := hbad (LineLocalWindow.output (PortLocalCompiler.translate t P) ids) hagree hclosed
  refine ⟨PortLocalCompiler.network ids,ids,PortLocalCompiler.compatible ids,hinj,
    TreewidthLocalLower.exact_identifiers ids hinj hIDs,?_⟩
  have hnon : 0 ≤ FractionalSolver.fractionalNumber (graph n t) := by
    obtain ⟨x,hx,heq⟩ := CoveringOptimum.exists_optimum_eq_number
      (fun v => (graph n t).neighborFinset v) Finset.univ (fun _ => (1:ℝ))
      (fun v _ => PathPowerTotal.isolate_free n t hn ht v) (fun _ => zero_le_one)
    change 0 ≤ CoveringOptimum.number _ _ _
    rw [← heq]
    exact Finset.sum_nonneg (fun v _ => mul_nonneg zero_le_one (hx.1 v))
  have hcost := mul_le_mul_of_nonneg_right (le_max_left c 0) hnon
  exact hcost.trans_lt (by simpa only [he] using hsize)

end Paper.TotalDomination.TreewidthFractionalLower
#print axioms Paper.TotalDomination.TreewidthFractionalLower.lower
