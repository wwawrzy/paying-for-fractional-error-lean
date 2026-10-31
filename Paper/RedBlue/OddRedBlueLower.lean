import Paper.RedBlue.OddRedBlueLocal
import Paper.Preliminaries.OddPairedGap
import Paper.Preliminaries.OddPathDegree
import Paper.Optimality.LowerBounds.OddPortCompiler
namespace Paper.OddRedBlue
open SevenFoundation

/-- Full red-blue limiting lower bound on connected planar degree-four
networks, with both fractional and integral optimum exactly m. -/
theorem lower (T : ℕ) (c : ℝ) (hc : c < 4) :
    ∃ m : ℕ, 0 < m ∧ (OddPathPower.graph (8*m) 3).Connected ∧
      (OddPathPower.graph (8*m) 3).IsPlanar ∧
      (∀ v, (OddPathPower.graph (8*m) 3).degree v ≤ 4) ∧
      (∀ p, CoveringOptimum.number
        (RedBlue.rows (OddPathPower.graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ))=m) ∧
      ∀ P : PortLocal.Program Bool Bool, P.rounds ≤ T →
        (∀ (p : Fin 2) (N : PortLocal.Network (Fin (8*m))), N.Compatible (OddPathPower.graph (8*m) 3) →
          ∀ ids : Fin (8*m) → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ 8*m) → Feasible N P ids p) →
        ∃ (N : PortLocal.Network (Fin (8*m))) (ids : Fin (8*m) → ℕ) (p : Fin 2),
          N.Compatible (OddPathPower.graph (8*m) 3) ∧ Function.Injective ids ∧
          Finset.univ.image ids=Finset.Icc 1 (8*m) ∧ Feasible N P ids p ∧
          c*CoveringOptimum.number
            (RedBlue.rows (OddPathPower.graph (8*m) 3) (red m p) (blue m p)) (red m p) (fun _ => (1:ℝ)) <
            (output N P ids p).card := by
  have hmax : max c 0 < 4 := max_lt hc (by norm_num)
  obtain ⟨m,hm,hwindow⟩ := OddPathPower.paired_window_lower_bound (3*(T+1)) (max c 0) (le_max_right _ _) hmax
  refine ⟨m,hm,OddPathPower.connected (8*m) (by omega),OddPathPower.planar (8*m),
    OddPathPower.degree_le_four (8*m),fractional_number m,?_⟩
  intro P hP hfeasible
  let Q := BipartiteTwin.program P
  have hQ : Q.rounds ≤ T := by simpa only [Q,BipartiteTwin.program_rounds] using hP
  have he (ids : Fin (8*m) → ℕ) :
      Finset.univ.filter (fun v => LineLocalWindow.output (OddPortCompiler.translate 3 Q) ids v=true) =
        TreewidthLocalLower.output (OddPortCompiler.network (t:=3) ids) Q ids := by
    ext v
    simp only [TreewidthLocalLower.output,Finset.mem_filter,Finset.mem_univ,true_and,LineLocalWindow.output]
    rw [OddPortCompiler.translate_correct Q ids (fun _ => ()) (fun _ => ()) (fun _ => rfl)]
  obtain ⟨ids,hinj,hIDs,hbad⟩ := hwindow (LineLocalWindow.rule (OddPortCompiler.translate 3 Q) (3*(T+1)))
  have hagree := LineLocalWindow.agrees (OddPortCompiler.translate 3 Q) (3*(T+1))
    (by
      unfold LineLocal.Program.radius
      rw [OddPortCompiler.rounds]
      nlinarith) ids
  let N := OddPortCompiler.network (t:=3) ids
  have hN : N.Compatible (OddPathPower.graph (8*m) 3) := OddPortCompiler.compatible ids
  have hF : ∀ p, Feasible N P ids p := fun p => hfeasible p N hN ids hinj hIDs
  have hdom : dominates (OddPathPower.graph (8*m) 3) (Finset.univ.filter
      (fun v => LineLocalWindow.output (OddPortCompiler.translate 3 Q) ids v=true)) := by
    rw [he]
    intro r
    obtain ⟨v,hv,ha⟩ := twin_total_dominates m N hN P ids hF r
    exact Finset.mem_biUnion.mpr ⟨v,hv,(mem_closed _ r v).mpr (Or.inr ha.symm)⟩
  have hsize := hbad _ hagree hdom
  rw [he] at hsize
  change 2*max c 0*m < ((TreewidthLocalLower.output N (BipartiteTwin.program P) ids).card:ℝ) at hsize
  rw [twin_output m N hN P ids] at hsize
  have hb : ∃ p : Fin 2, c*(m:ℝ) < (output N P ids p).card := by
    by_contra hn
    push_neg at hn
    have h0 := hn (0:Fin 2)
    have h1 := hn (1:Fin 2)
    have hu : (((output N P ids 0 ∪ output N P ids 1).card):ℝ) ≤
        (output N P ids 0).card+(output N P ids 1).card := by exact_mod_cast Finset.card_union_le _ _
    have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have hcM := mul_le_mul_of_nonneg_right (le_max_left c 0) hmR
    linarith
  obtain ⟨p,hp⟩ := hb
  refine ⟨N,ids,p,hN,hinj,TreewidthLocalLower.exact_identifiers ids hinj hIDs,hF p,?_⟩
  rw [fractional_number]
  exact hp
end Paper.OddRedBlue
#print axioms Paper.OddRedBlue.lower
