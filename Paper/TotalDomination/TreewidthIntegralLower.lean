import Paper.TotalDomination.PathTotalIntegralGap
import Paper.TotalDomination.TreewidthFractionalLower
import Paper.Endpoints.Girth.HighGirthPathFamily

/-! The integral-total-optimum strengthening for t=1 in fv:total:lower-tw. -/
namespace Paper.TotalDomination.TreewidthIntegralLower
open SevenFoundation PathPowerTreewidth

theorem lower (T : ℕ) (c : ℝ) (hct : c < 2) :
    ∃ n : ℕ, 2 ≤ n ∧ (graph n 1).Connected ∧ graph n 1 = SimpleGraph.pathGraph n ∧ (graph n 1).treeWidth ≤ 1 ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (graph n 1) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (graph n 1).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (graph n 1) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*((graph n 1).totalDominationNumber:ℝ) < (TreewidthLocalLower.output N P ids).card := by
  have hmax : max c 0 < 2 := max_lt hct (by norm_num)
  obtain ⟨n,hn,hwindow⟩ := PathTotalIntegralGap.window_lower_bound (T+1) (max c 0) (le_max_right _ _) hmax
  refine ⟨n,hn,TreewidthFractionalLower.connected n 1 (by omega) (by decide),
    HighGirthPathFamily.first_power_eq_path n,treeWidth_le n 1,?_⟩
  intro P hP hdom
  have he (ids : Fin n → ℕ) :
      Finset.univ.filter (fun v => LineLocalWindow.output (PortLocalCompiler.translate 1 P) ids v = true) =
        TreewidthLocalLower.output (PortLocalCompiler.network (t := 1) ids) P ids := by
    ext v
    simp only [TreewidthLocalLower.output,Finset.mem_filter,Finset.mem_univ,true_and,LineLocalWindow.output]
    rw [PortLocalCompiler.translate_correct P ids (fun _ => ()) (fun _ => ()) (fun _ => rfl)]
  obtain ⟨ids,hinj,hIDs,hbad⟩ := hwindow (LineLocalWindow.rule (PortLocalCompiler.translate 1 P) (T+1))
  have hagree := LineLocalWindow.agrees (PortLocalCompiler.translate 1 P) (T+1)
    (by
      unfold LineLocal.Program.radius
      rw [PortLocalCompiler.rounds]
      nlinarith) ids
  have hclosed : dominates (graph n 1) (Finset.univ.filter
      (fun v => LineLocalWindow.output (PortLocalCompiler.translate 1 P) ids v = true)) := by
    rw [he]
    intro r
    obtain ⟨v,hv,ha⟩ := hdom _ (PortLocalCompiler.compatible ids) ids hinj hIDs r
    exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_closed (graph n 1) r v).mpr (Or.inr ha.symm)⟩
  have hsize := hbad (LineLocalWindow.output (PortLocalCompiler.translate 1 P) ids) hagree hclosed
  refine ⟨PortLocalCompiler.network ids,ids,PortLocalCompiler.compatible ids,hinj,
    TreewidthLocalLower.exact_identifiers ids hinj hIDs,?_⟩
  have hnon : (0:ℝ) ≤ ((graph n 1).totalDominationNumber:ℝ) := Nat.cast_nonneg _
  have hcost := mul_le_mul_of_nonneg_right (le_max_left c 0) hnon
  exact hcost.trans_lt (by simpa only [he] using hsize)

end Paper.TotalDomination.TreewidthIntegralLower
#print axioms Paper.TotalDomination.TreewidthIntegralLower.lower
