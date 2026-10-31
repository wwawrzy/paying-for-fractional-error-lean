import Paper.Optimality.LowerBounds.OddPortCompiler
import Paper.Preliminaries.OddPathGap
import Paper.TotalDomination.TreewidthFractionalLower
namespace Paper.TotalDomination.PlanarTotalLower
open SevenFoundation

theorem triangle_free (T : ℕ) (c : ℝ) (hc : c < 4) :
    ∃ n : ℕ, 2 ≤ n ∧ (OddPathPower.graph n 3).Connected ∧ (OddPathPower.graph n 3).IsPlanar ∧
      (∀ v, ((OddPathPower.graph n 3).neighborFinset v).Nonempty) ∧
      (∀ (v : Fin n) (p : (OddPathPower.graph n 3).Walk v v), p.IsCycle → 4 ≤ p.length) ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (OddPathPower.graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (OddPathPower.graph n 3).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (OddPathPower.graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*FractionalSolver.fractionalNumber (OddPathPower.graph n 3) < (TreewidthLocalLower.output N P ids).card := by
  have hmax : max c 0 < 4 := max_lt hc (by norm_num)
  obtain ⟨n,hn,hwindow⟩ := OddPathPower.window_lower_bound (3*(T+1)) (max c 0) (le_max_right _ _) hmax
  refine ⟨n,hn,OddPathPower.connected n (by omega),OddPathPower.planar n,
    OddPathPower.isolate_free n hn,OddPathPower.girth_four,?_⟩
  intro P hP hdom
  have he (ids : Fin n → ℕ) :
      Finset.univ.filter (fun v => LineLocalWindow.output (OddPortCompiler.translate 3 P) ids v = true) =
        TreewidthLocalLower.output (OddPortCompiler.network (t := 3) ids) P ids := by
    ext v
    simp only [TreewidthLocalLower.output,Finset.mem_filter,Finset.mem_univ,true_and,LineLocalWindow.output]
    rw [OddPortCompiler.translate_correct P ids (fun _ => ()) (fun _ => ()) (fun _ => rfl)]
  obtain ⟨ids,hinj,hIDs,hbad⟩ := hwindow (LineLocalWindow.rule (OddPortCompiler.translate 3 P) (3*(T+1)))
  have hagree := LineLocalWindow.agrees (OddPortCompiler.translate 3 P) (3*(T+1))
    (by
      unfold LineLocal.Program.radius
      rw [OddPortCompiler.rounds]
      nlinarith) ids
  have hclosed : dominates (OddPathPower.graph n 3) (Finset.univ.filter
      (fun v => LineLocalWindow.output (OddPortCompiler.translate 3 P) ids v = true)) := by
    rw [he]
    intro r
    obtain ⟨v,hv,ha⟩ := hdom _ (OddPortCompiler.compatible ids) ids hinj hIDs r
    exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_closed (OddPathPower.graph n 3) r v).mpr (Or.inr ha.symm)⟩
  have hsize := hbad (LineLocalWindow.output (OddPortCompiler.translate 3 P) ids) hagree hclosed
  refine ⟨OddPortCompiler.network ids,ids,OddPortCompiler.compatible ids,hinj,
    TreewidthLocalLower.exact_identifiers ids hinj hIDs,?_⟩
  have hnon : 0 ≤ FractionalSolver.fractionalNumber (OddPathPower.graph n 3) := by
    obtain ⟨x,hx,heq⟩ := CoveringOptimum.exists_optimum_eq_number
      (fun v => (OddPathPower.graph n 3).neighborFinset v) Finset.univ (fun _ => (1:ℝ))
      (fun v _ => OddPathPower.isolate_free n hn v) (fun _ => zero_le_one)
    change 0 ≤ CoveringOptimum.number _ _ _
    rw [← heq]
    exact Finset.sum_nonneg (fun v _ => mul_nonneg zero_le_one (hx.1 v))
  have hcost := mul_le_mul_of_nonneg_right (le_max_left c 0) hnon
  exact hcost.trans_lt (by simpa only [he] using hsize)


#print axioms Paper.TotalDomination.PlanarTotalLower.triangle_free

/-- The coefficient-six branch on connected planar third powers of paths. -/
theorem planar (T : ℕ) (c : ℝ) (hc : c < 6) :
    ∃ n : ℕ, 2 ≤ n ∧ (PathPowerTreewidth.graph n 3).Connected ∧ (PathPowerTreewidth.graph n 3).IsPlanar ∧
      (∀ v, ((PathPowerTreewidth.graph n 3).neighborFinset v).Nonempty) ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (PathPowerTreewidth.graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          ∀ r, ∃ v ∈ TreewidthLocalLower.output N P ids, (PathPowerTreewidth.graph n 3).Adj r v) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (PathPowerTreewidth.graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*FractionalSolver.fractionalNumber (PathPowerTreewidth.graph n 3) < (TreewidthLocalLower.output N P ids).card := by
  obtain ⟨n,hn,hconn,htw,hbad⟩ := TreewidthFractionalLower.lower 3 T (by decide) c (by norm_num;exact hc)
  exact ⟨n,hn,hconn,PathPowerThreePlanar.isPlanar n,PathPowerTotal.isolate_free n 3 hn (by decide),hbad⟩

end Paper.TotalDomination.PlanarTotalLower
#print axioms Paper.TotalDomination.PlanarTotalLower.planar
