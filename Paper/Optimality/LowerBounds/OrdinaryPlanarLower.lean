import Paper.Preliminaries.OddOrdinaryGap
import Paper.Optimality.LowerBounds.OddPortCompiler
import Paper.Optimality.LowerBounds.TreewidthLocalLower
namespace Paper.OrdinaryPlanarLower
open SevenFoundation
theorem triangle_free (T : ℕ) (c : ℝ) (hc : c < 5) :
    ∃ n : ℕ, 2 ≤ n ∧ (OddPathPower.graph n 3).Connected ∧ (OddPathPower.graph n 3).IsPlanar ∧
      (∀ v, ((OddPathPower.graph n 3).neighborFinset v).Nonempty) ∧
      (∀ (v : Fin n) (p : (OddPathPower.graph n 3).Walk v v), p.IsCycle → 4 ≤ p.length) ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (OddPathPower.graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          dominates (OddPathPower.graph n 3) (TreewidthLocalLower.output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (OddPathPower.graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*((OddPathPower.graph n 3).dominationNumber:ℝ) < (TreewidthLocalLower.output N P ids).card := by
  have hmax : max c 0 < 5 := max_lt hc (by norm_num)
  obtain ⟨n,hn,hwindow⟩ := OddPathPower.ordinary_window_lower_bound (3*(T+1)) (max c 0) (le_max_right _ _) hmax
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
    exact hdom _ (OddPortCompiler.compatible ids) ids hinj hIDs
  have hsize := hbad (LineLocalWindow.output (OddPortCompiler.translate 3 P) ids) hagree hclosed
  refine ⟨OddPortCompiler.network ids,ids,OddPortCompiler.compatible ids,hinj,
    TreewidthLocalLower.exact_identifiers ids hinj hIDs,?_⟩
  have hnon : (0:ℝ) ≤ ((OddPathPower.graph n 3).dominationNumber:ℝ) := Nat.cast_nonneg _
  have hcost := mul_le_mul_of_nonneg_right (le_max_left c 0) hnon
  exact hcost.trans_lt (by simpa only [he] using hsize)





#print axioms Paper.OrdinaryPlanarLower.triangle_free

theorem planar (T : ℕ) (c : ℝ) (hc : c < 7) :
    ∃ n : ℕ, 0 < n ∧ (PathPowerTreewidth.graph n 3).IsPlanar ∧
      ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (PathPowerTreewidth.graph n 3) →
          ∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          dominates (PathPowerTreewidth.graph n 3) (TreewidthLocalLower.output N P ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
          N.Compatible (PathPowerTreewidth.graph n 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c*((PathPowerTreewidth.graph n 3).dominationNumber:ℝ) < (TreewidthLocalLower.output N P ids).card := by
  obtain ⟨n,hn,htw,hbad⟩ := TreewidthLocalLower.exact_lower 3 T c (by norm_num;exact hc)
  exact ⟨n,hn,PathPowerThreePlanar.isPlanar n,hbad⟩
end Paper.OrdinaryPlanarLower
#print axioms Paper.OrdinaryPlanarLower.planar
