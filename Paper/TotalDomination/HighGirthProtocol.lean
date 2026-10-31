import Paper.TotalDomination.HighGirthStartup
import Paper.Communication.ProgramMemory
namespace Paper.TotalDomination.HighGirthProtocol
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
structure Input where
  base : Protocol.Input
  linked : Bool

def prepareRound : Round V (Protocol.HighState × Bool) (GeneralCoveringRequests.Input V) Bool where
  send _ _ s := s.1.high
  update v N s msg :=
    ⟨s.1.input.first || s.1.high,
      s.1.residual && decide (Protocol.near v N msg = ∅) && !s.2,s.1.input.demand,N⟩
def program {b : ℕ} (ids : BitCode V b) : Program V Input Bool :=
  .seq (.local fun _ _ s => (s.base,s.linked))
    (.seq (ProgramMemory.carry (X := Bool)
      (.seq (.broadcast 1 BitCode.bool Protocol.residualRound)
        (.broadcast 1 BitCode.bool (Protocol.highRound 3))))
      (.seq (.broadcast 1 BitCode.bool prepareRound)
        (.seq (.broadcast (b+1) ids.option GeneralCoveringRequests.selectRound)
          (.local fun _ _ s => s.selected))))
theorem rounds {b : ℕ} (ids : BitCode V b) : (program ids).rounds=4 := rfl
theorem maxBits {b : ℕ} (ids : BitCode V b) : (program ids).maxBits ≤ b+1 := by
  change max 0 (max (max 1 1) (max 1 (max (b+1) 0))) ≤ b+1
  omega
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (labels : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
variable (s : V → Input)
local notation "I" => HighGirthSetup.I G x labels hfree
local notation "W" => first G I
local notation "R" => residual G I
local notation "H" => high G I
local notation "U" => last G I
local notation "Req" => HighGirthSetup.requests G x labels hfree

theorem prepare_correct
    (hdemand : ∀ v, (s v).base.demand=decide (v ∈ HighGirthSetup.Z G))
    (hfirst : ∀ v, (s v).base.first=decide (v ∈ W))
    (hlinked : ∀ v, (s v).linked=decide (v ∈ HighGirthStartup.linked G)) :
    eval G prepareRound (fun v => (Protocol.HighState.mk (s v).base (decide (v ∈ R)) (decide (v ∈ H)),(s v).linked)) =
      fun v => ⟨decide (v ∈ W ∪ H),decide (v ∈ Req),decide (v ∈ HighGirthSetup.Z G),G.neighborFinset v⟩ := by
  funext v
  have hp := congrFun (Protocol.prepare_correct G I (fun v => (s v).base) hdemand hfirst) v
  have hrow : ((s v).base.first || decide (v ∈ H))=decide (v ∈ W ∪ H) := by
    rw [hfirst]; simp only [Finset.mem_union,Bool.decide_or]
  have hu : (decide (v ∈ R) && decide (Protocol.near v (G.neighborFinset v)
      (fun u => decide (u.val ∈ H)) = ∅)) = decide (v ∈ U) := by
    exact congrArg GeneralCoveringRequests.Input.requester hp
  change GeneralCoveringRequests.Input.mk
    ((s v).base.first || decide (v ∈ H))
    ((decide (v ∈ R) && decide (Protocol.near v (G.neighborFinset v)
      (fun u => decide (u.val ∈ H)) = ∅)) && !(s v).linked) (s v).base.demand _ = _
  rw [hrow,hu,hdemand,hlinked]
  congr 1
  rw [←decide_not,←Bool.decide_and]
  apply Bool.decide_congr
  have hUZ : v ∈ U → v ∈ HighGirthSetup.Z G := fun h =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
  simp only [HighGirthSetup.requests,HighGirthSetup.linkedLast,HighGirthStartup.linked,
    Finset.mem_sdiff,Finset.mem_inter]
  tauto

theorem requested_eq_image (hmono : StrictMono labels) :
    GeneralCoveringRequests.requested (fun r => G.neighborFinset r) Req = (Req).image (request G I) := by
  ext v
  rw [GeneralCoveringRequests.mem_requested]
  simp only [Protocol.minimum_eq_request G I hmono,Option.some.injEq,Finset.mem_image]

theorem run_eq {b : ℕ} (ids : BitCode V b)
    (hcandidate : ∀ v, (s v).base.candidate=decide (v ∈ HighGirthSetup.K G))
    (hdemand : ∀ v, (s v).base.demand=decide (v ∈ HighGirthSetup.Z G))
    (hfirst : ∀ v, (s v).base.first=decide (v ∈ W))
    (hlinked : ∀ v, (s v).linked=decide (v ∈ HighGirthStartup.linked G))
    (hmono : StrictMono labels) :
    (program ids).runEncoded G s = fun v => decide (v ∈ HighGirthSetup.selected G x labels hfree) := by
  rw [Program.runEncoded_eq_run]
  simp only [program,Program.run,ProgramMemory.run]
  have hr := Protocol.residual_correct G I (fun v => (s v).base) hdemand hfirst
  have hh := Protocol.high_correct G I (fun v => (s v).base) hcandidate hfirst
  change eval G Protocol.residualRound (fun v => (s v).base) = _ at hr
  change eval G (Protocol.highRound 3) _ = _ at hh
  rw [hr,hh,prepare_correct G x labels hfree s hdemand hfirst hlinked]
  rw [GeneralCoveringRequests.select_correct G (fun r => G.neighborFinset r) (W ∪ H) Req
    (fun v => ⟨decide (v ∈ W ∪ H),decide (v ∈ Req),decide (v ∈ HighGirthSetup.Z G),G.neighborFinset v⟩)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by
      intro r _ v hv
      exact (mem_closed G v r).mpr (Or.inr ((G.mem_neighborFinset r v).mp hv)))]
  rw [GeneralCoveringRequests.selectedPlus,requested_eq_image G x labels hfree hmono]
  rfl
end Paper.TotalDomination.HighGirthProtocol
#print axioms Paper.TotalDomination.HighGirthProtocol.run_eq
