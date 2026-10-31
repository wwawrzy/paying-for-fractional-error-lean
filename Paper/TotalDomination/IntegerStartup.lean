import Paper.TotalDomination.IntegerSetup
import Paper.TotalDomination.Protocol
import Paper.Communication.ClosedBitProgram
import Paper.Solver.LocalSearch.GeneralCoveringFractionalEndpoint

/-! Five one-bit broadcasts construct the actual integer residual LP input.
All neighborhood lists stay in private local memory. -/
namespace Paper.TotalDomination.IntegerStartup
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure BudgetState where
  selected : Bool
  cost : ℕ
  linked : Bool

structure Output (V : Type) (d : ℕ) where
  solver : GeneralCoveringFractionalEndpoint.Input V d
  selected : Bool
  linked : Bool

def selectRound : Round V Bool Bool Bool where
  send _ _ s := s
  update v N s msg := s && decide (Protocol.near v N msg).Nonempty

def budgetRound (d : ℕ) : Round V Bool BudgetState Bool where
  send _ _ s := s
  update v N s msg :=
    ⟨s,d-(Protocol.near v N msg).card,!s && decide (Protocol.near v N msg).Nonempty⟩

def candidateRound (d : ℕ) : Round V BudgetState (Output V d) Bool where
  send _ _ s := decide (0 < s.cost)
  update v N s msg :=
    ⟨(⟨!s.selected,Protocol.near v N msg,if 0 < s.cost then N else ∅⟩,
      ⟨min s.cost d,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩),s.selected,s.linked⟩

def program (d : ℕ) : Program V PUnit (Output V d) :=
  .seq (.local fun _ N _ => decide (N.card ≠ d))
    (.seq ClosedBitProgram.closure
      (.seq ClosedBitProgram.closure
        (.seq (.local fun _ _ s => !s)
          (.seq (.broadcast 1 BitCode.bool selectRound)
            (.seq (.broadcast 1 BitCode.bool (budgetRound d))
              (.broadcast 1 BitCode.bool (candidateRound d)))))))

theorem rounds (d : ℕ) : (program (V := V) d).rounds = 5 := rfl
theorem maxBits (d : ℕ) : (program (V := V) d).maxBits = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

def input (v : V) : GeneralCoveringFractionalEndpoint.Input V d :=
  (⟨decide (v ∈ IntegerSetup.Z G d),G.neighborFinset v ∩ IntegerSetup.K G d,
    if v ∈ IntegerSetup.K G d then G.neighborFinset v else ∅⟩,
    ⟨IntegerSetup.c G d v,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)

theorem select_correct :
    eval G selectRound (fun v => decide (v ∈ WeightedBudget.far G d)) =
      fun v => decide (v ∈ IntegerSetup.F G d) := by
  funext v
  change (decide (v ∈ WeightedBudget.far G d) && decide
    (Protocol.near v (G.neighborFinset v) (fun u => decide (u.val ∈ WeightedBudget.far G d))).Nonempty) = _
  rw [Protocol.near_correct]
  simp only [IntegerSetup.F,InitialSelection.selected,Finset.mem_filter,Bool.decide_and]

theorem budget_correct :
    eval G (budgetRound d) (fun v => decide (v ∈ IntegerSetup.F G d)) =
      fun v => ⟨decide (v ∈ IntegerSetup.F G d),IntegerSetup.c G d v,
        decide (v ∈ IntegerSetup.linked G d)⟩ := by
  funext v
  change BudgetState.mk _ _ _ = _
  simp only [budgetRound,Protocol.near_correct]
  have hn : (G.neighborFinset v ∩ IntegerSetup.F G d).Nonempty ↔
      v ∈ neighbors G (IntegerSetup.F G d) := by
    rw [Finset.nonempty_iff_ne_empty]
    exact not_iff_not.mpr (Protocol.near_empty_iff G (IntegerSetup.F G d) v) |>.trans not_not
  simp only [IntegerSetup.c,InitialSelection.boundaryCost,InitialSelection.hits,
    IntegerSetup.linked,IntegerSetup.Z,InitialSelection.remaining,Finset.mem_inter,
    Finset.mem_sdiff,Finset.mem_univ,true_and,hn,decide_not,Bool.decide_and]

theorem candidate_correct :
    eval G (candidateRound d) (fun v => ⟨decide (v ∈ IntegerSetup.F G d),IntegerSetup.c G d v,
      decide (v ∈ IntegerSetup.linked G d)⟩) =
      fun v => ⟨input G d v,decide (v ∈ IntegerSetup.F G d),decide (v ∈ IntegerSetup.linked G d)⟩ := by
  funext v
  have hk : (fun u => decide (0 < IntegerSetup.c G d u)) =
      fun u => decide (u ∈ IntegerSetup.K G d) := by
    funext u
    simp only [IntegerSetup.K,InitialSelection.candidates,Finset.mem_filter,Finset.mem_univ,true_and]
  change Output.mk _ _ _ = _
  simp only [candidateRound]
  have hm : min (IntegerSetup.c G d v) d = IntegerSetup.c G d v :=
    Nat.min_eq_left (Nat.sub_le _ _)
  have hnear : Protocol.near v (G.neighborFinset v)
      (fun u => decide (0 < IntegerSetup.c G d u.val)) = G.neighborFinset v ∩ IntegerSetup.K G d := by
    have he : (fun u : G.neighborFinset v => decide (0 < IntegerSetup.c G d u.val)) =
        (fun u : G.neighborFinset v => decide (u.val ∈ IntegerSetup.K G d)) := by
      funext u
      exact congrFun hk u.val
    rw [he,Protocol.near_correct]
  simp only [hnear,hm,input,IntegerSetup.Z,InitialSelection.remaining,Finset.mem_sdiff,
    Finset.mem_univ,true_and,decide_not]
  congr 4
  simp only [IntegerSetup.K,InitialSelection.candidates,Finset.mem_filter,Finset.mem_univ,true_and]

theorem correct :
    (program d).run G (fun _ => PUnit.unit) =
      fun v => ⟨input G d v,decide (v ∈ IntegerSetup.F G d),decide (v ∈ IntegerSetup.linked G d)⟩ := by
  have hinit : (fun v => decide ((G.neighborFinset v).card ≠ d)) =
      fun v => decide (v ∈ WeightedBudget.defects G d) := by
    funext v
    simp only [WeightedBudget.defects,Finset.mem_filter,Finset.mem_univ,true_and,
      SimpleGraph.card_neighborFinset_eq_degree]
    rfl
  have hfar : (fun v => !decide (v ∈ covered G (covered G (WeightedBudget.defects G d)))) =
      fun v => decide (v ∈ WeightedBudget.far G d) := by
    funext v
    simp only [WeightedBudget.far,WeightedBudget.zone,Finset.mem_sdiff,Finset.mem_univ,true_and,decide_not]
  simp only [program,Program.run]
  rw [hinit,ClosedBitProgram.closure_correct,ClosedBitProgram.closure_correct]
  change eval G (candidateRound d) (eval G (budgetRound d)
    (eval G selectRound (fun v => !decide (v ∈ covered G (covered G (WeightedBudget.defects G d)))))) = _
  rw [hfar,select_correct,budget_correct,candidate_correct]


def original (hd : 0 < d) (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    GeneralCoveringInitializedFrameAverage.Original G (input G d) where
  cover := fun r => G.neighborFinset r ∩ IntegerSetup.K G d
  targets := fun v => if v ∈ IntegerSetup.K G d then G.neighborFinset v else ∅
  R := IntegerSetup.Z G d
  incidence := fun v r => by
    by_cases hv : v ∈ IntegerSetup.K G d <;>
      simp only [hv,if_true,if_false,Finset.mem_inter,Finset.notMem_empty,and_false,
        and_true,SimpleGraph.mem_neighborFinset,G.adj_comm]
  local_rows := fun r _ v hv => (mem_closed G v r).mpr
    (Or.inr ((G.mem_neighborFinset r v).mp (Finset.mem_inter.mp hv).1))
  rows := fun r hr => by
    rw [InitialSelection.demand_rows G d hd hr]
    exact hfree r
  residual := fun _ => rfl
  candidates := fun _ => rfl
  inverse := fun _ => rfl

theorem admissible_subset :
    CoveringSupport.admissible (fun r => G.neighborFinset r ∩ IntegerSetup.K G d)
      (IntegerSetup.Z G d) ⊆ IntegerSetup.K G d := by
  intro v hv
  obtain ⟨r,hr,hv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_inter.mp hv).2

theorem positive_cost : ∀ v ∈ CoveringSupport.admissible
    (fun r => G.neighborFinset r ∩ IntegerSetup.K G d) (IntegerSetup.Z G d),
    1 ≤ ((input G d v).2.val) := by
  intro v hv
  have hk := admissible_subset G d hv
  have hp : 0 < IntegerSetup.c G d v := (Finset.mem_filter.mp hk).2
  exact hp

end Paper.TotalDomination.IntegerStartup
#print axioms Paper.TotalDomination.IntegerStartup.correct
