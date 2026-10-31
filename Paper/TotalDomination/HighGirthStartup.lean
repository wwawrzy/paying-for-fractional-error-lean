import Paper.TotalDomination.IntegerStartup
import Paper.TotalDomination.HighGirthSetup
namespace Paper.TotalDomination.HighGirthStartup
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
abbrev BudgetState := IntegerStartup.BudgetState
abbrev Output (V : Type) := IntegerStartup.Output V 2

def program : Program V PUnit (Output V) :=
  .seq (.local fun _ N _ => decide (3 ≤ N.card))
    (.seq ClosedBitProgram.closure
      (.seq ClosedBitProgram.closure
        (.seq (.local fun _ _ s => !s)
          (.seq (.broadcast 1 BitCode.bool IntegerStartup.selectRound)
            (.seq (.broadcast 1 BitCode.bool (IntegerStartup.budgetRound 2))
              (.broadcast 1 BitCode.bool (IntegerStartup.candidateRound 2)))))))
theorem rounds : (program (V := V)).rounds=5 := rfl
theorem maxBits : (program (V := V)).maxBits=1 := rfl
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def linked : Finset V := HighGirthSetup.Z G ∩ neighbors G (HighGirthSetup.F G)
def input (v : V) : GeneralCoveringFractionalEndpoint.Input V 2 :=
  (⟨decide (v ∈ HighGirthSetup.Z G),G.neighborFinset v ∩ HighGirthSetup.K G,
    if v ∈ HighGirthSetup.K G then G.neighborFinset v else ∅⟩,
    ⟨HighGirthSetup.c G v,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
theorem select_correct :
    eval G IntegerStartup.selectRound (fun v => decide (v ∈ HighGirthSelection.far G)) =
      fun v => decide (v ∈ HighGirthSetup.F G) := by
  funext v
  change (decide (v ∈ HighGirthSelection.far G) && decide
    (Protocol.near v (G.neighborFinset v) (fun u => decide (u.val ∈ HighGirthSelection.far G))).Nonempty) = _
  rw [Protocol.near_correct]
  simp only [HighGirthSetup.F,HighGirthSelection.selected,Finset.mem_filter,Bool.decide_and]

theorem budget_correct :
    eval G (IntegerStartup.budgetRound 2) (fun v => decide (v ∈ HighGirthSetup.F G)) =
      fun v => ⟨decide (v ∈ HighGirthSetup.F G),HighGirthSetup.c G v,
        decide (v ∈ linked G)⟩ := by
  funext v
  change IntegerStartup.BudgetState.mk _ _ _ = _
  simp only [IntegerStartup.budgetRound,Protocol.near_correct]
  have hn : (G.neighborFinset v ∩ HighGirthSetup.F G).Nonempty ↔
      v ∈ neighbors G (HighGirthSetup.F G) := by
    rw [Finset.nonempty_iff_ne_empty]
    exact not_iff_not.mpr (Protocol.near_empty_iff G (HighGirthSetup.F G) v) |>.trans not_not
  simp only [HighGirthSetup.c,HighGirthSelection.boundaryCost,HighGirthSelection.hits,
    linked,HighGirthSetup.Z,HighGirthSelection.remaining,Finset.mem_inter,
    Finset.mem_sdiff,Finset.mem_univ,true_and,hn,decide_not,Bool.decide_and]

theorem candidate_correct :
    eval G (IntegerStartup.candidateRound 2) (fun v => ⟨decide (v ∈ HighGirthSetup.F G),HighGirthSetup.c G v,
      decide (v ∈ linked G)⟩) =
      fun v => ⟨input G v,decide (v ∈ HighGirthSetup.F G),decide (v ∈ linked G)⟩ := by
  funext v
  have hk : (fun u => decide (0 < HighGirthSetup.c G u)) =
      fun u => decide (u ∈ HighGirthSetup.K G) := by
    funext u
    simp only [HighGirthSetup.K,HighGirthSelection.candidates,Finset.mem_filter,Finset.mem_univ,true_and]
  change IntegerStartup.Output.mk _ _ _ = _
  simp only [IntegerStartup.candidateRound]
  have hm : min (HighGirthSetup.c G v) 2 = HighGirthSetup.c G v :=
    Nat.min_eq_left (Nat.sub_le _ _)
  have hnear : Protocol.near v (G.neighborFinset v)
      (fun u => decide (0 < HighGirthSetup.c G u.val)) = G.neighborFinset v ∩ HighGirthSetup.K G := by
    have he : (fun u : G.neighborFinset v => decide (0 < HighGirthSetup.c G u.val)) =
        (fun u : G.neighborFinset v => decide (u.val ∈ HighGirthSetup.K G)) := by
      funext u
      exact congrFun hk u.val
    rw [he,Protocol.near_correct]
  simp only [hnear,hm,input,HighGirthSetup.Z,HighGirthSelection.remaining,Finset.mem_sdiff,
    Finset.mem_univ,true_and,decide_not]
  congr 4
  simp only [HighGirthSetup.K,HighGirthSelection.candidates,Finset.mem_filter,Finset.mem_univ,true_and]

theorem correct :
    (program).run G (fun _ => PUnit.unit) =
      fun v => ⟨input G v,decide (v ∈ HighGirthSetup.F G),decide (v ∈ linked G)⟩ := by
  have hinit : (fun v => decide ((G.neighborFinset v).card ≥ 3)) =
      fun v => decide (v ∈ HighGirthSelection.branch G) := by
    funext v
    simp only [HighGirthSelection.branch,Finset.mem_filter,Finset.mem_univ,true_and,
      SimpleGraph.card_neighborFinset_eq_degree]
    rfl
  have hfar : (fun v => !decide (v ∈ covered G (covered G (HighGirthSelection.branch G)))) =
      fun v => decide (v ∈ HighGirthSelection.far G) := by
    funext v
    simp only [HighGirthSelection.far,HighGirthSelection.zone,Finset.mem_sdiff,Finset.mem_univ,true_and,decide_not]
  simp only [program,Program.run]
  rw [hinit,ClosedBitProgram.closure_correct,ClosedBitProgram.closure_correct]
  change eval G (IntegerStartup.candidateRound 2) (eval G (IntegerStartup.budgetRound 2)
    (eval G IntegerStartup.selectRound (fun v => !decide (v ∈ covered G (covered G (HighGirthSelection.branch G)))))) = _
  rw [hfar,select_correct,budget_correct,candidate_correct]


def original (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    GeneralCoveringInitializedFrameAverage.Original G (input G) where
  cover := fun r => G.neighborFinset r ∩ HighGirthSetup.K G
  targets := fun v => if v ∈ HighGirthSetup.K G then G.neighborFinset v else ∅
  R := HighGirthSetup.Z G
  incidence := fun v r => by
    by_cases hv : v ∈ HighGirthSetup.K G <;>
      simp only [hv,if_true,if_false,Finset.mem_inter,Finset.notMem_empty,and_false,
        and_true,SimpleGraph.mem_neighborFinset,G.adj_comm]
  local_rows := fun r _ v hv => (mem_closed G v r).mpr
    (Or.inr ((G.mem_neighborFinset r v).mp (Finset.mem_inter.mp hv).1))
  rows := fun r hr => by
    rw [HighGirthSelection.demand_rows G hr]
    exact hfree r
  residual := fun _ => rfl
  candidates := fun _ => rfl
  inverse := fun _ => rfl

theorem admissible_subset :
    CoveringSupport.admissible (fun r => G.neighborFinset r ∩ HighGirthSetup.K G)
      (HighGirthSetup.Z G) ⊆ HighGirthSetup.K G := by
  intro v hv
  obtain ⟨r,hr,hv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_inter.mp hv).2

theorem positive_cost : ∀ v ∈ CoveringSupport.admissible
    (fun r => G.neighborFinset r ∩ HighGirthSetup.K G) (HighGirthSetup.Z G),
    1 ≤ ((input G v).2.val) := by
  intro v hv
  have hk := admissible_subset G hv
  have hp : 0 < HighGirthSetup.c G v := (Finset.mem_filter.mp hk).2
  exact hp


end Paper.TotalDomination.HighGirthStartup
#print axioms Paper.TotalDomination.HighGirthStartup.correct
