import Paper.TotalDomination.HighGirthProtocol
import Paper.TotalDomination.EncodedRounding
import Paper.TotalDomination.HighGirthMathematicalEndpoint
namespace Paper.TotalDomination.HighGirthVectorRounding
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
structure Input (V : Type) where
  startup : HighGirthStartup.Output V
  value : ℝ

noncomputable def prepare (N : Finset V) (s : Input V) : HighGirthProtocol.Input := by
  classical
  exact
  ⟨⟨decide (0 < s.startup.solver.2.val),!s.startup.selected,
    decide (0 < s.startup.solver.2.val) && decide (3 ≤ N.card) &&
      decide ((2:ℝ)/3 < s.value)⟩,s.startup.linked⟩
noncomputable def rounding {ids : ℕ} (codec : BitCode V ids) : Program V (Input V) Bool :=
  .seq (.local fun _ N s => (prepare N s,s.startup.selected))
    (.seq (ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec))
      (.local fun _ _ s => s.1 || s.2))
theorem rounding_rounds {ids : ℕ} (codec : BitCode V ids) :
    (rounding codec).rounds=4 := by
  simp only [rounding,Program.rounds,ProgramMemory.rounds,HighGirthProtocol.rounds,Nat.zero_add,Nat.add_zero]
theorem rounding_maxBits {ids : ℕ} (codec : BitCode V ids) :
    (rounding codec).maxBits ≤ ids+1 := by
  simp only [rounding,Program.maxBits,ProgramMemory.maxBits,Nat.zero_max,Nat.max_zero]
  exact HighGirthProtocol.maxBits codec
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def localInput (x : V → ℝ) (v : V) : Input V :=
  ⟨⟨HighGirthStartup.input G v,decide (v ∈ HighGirthSetup.F G),decide (v ∈ HighGirthStartup.linked G)⟩,x v⟩
theorem candidate_correct (x : V → ℝ) (v : V) :
    (prepare (G.neighborFinset v) (localInput G x v)).base.candidate =
      decide (v ∈ HighGirthSetup.K G) := by
  classical
  simp only [prepare,localInput,HighGirthStartup.input,HighGirthSetup.K,HighGirthSelection.candidates,
    Finset.mem_filter,Finset.mem_univ,true_and]
theorem demand_correct (x : V → ℝ) (v : V) :
    (prepare (G.neighborFinset v) (localInput G x v)).base.demand =
      decide (v ∈ HighGirthSetup.Z G) := by
  classical
  simp only [prepare,localInput,HighGirthSetup.Z,HighGirthSelection.remaining,
    Finset.mem_sdiff,Finset.mem_univ,true_and,decide_not]
theorem linked_correct (x : V → ℝ) (v : V) :
    (prepare (G.neighborFinset v) (localInput G x v)).linked =
      decide (v ∈ HighGirthStartup.linked G) := rfl
theorem first_correct (x : V → ℝ) (labels : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) (v : V) :
    (prepare (G.neighborFinset v) (localInput G x v)).base.first =
      decide (v ∈ first G (HighGirthSetup.I G
        x labels hfree)) := by
  classical
  rw [show (prepare (G.neighborFinset v) (localInput G x v)).base.first =
      (decide (v ∈ HighGirthSetup.K G) && decide (v ∈ HighGirthSetup.B G) &&
        decide ((2:ℝ)/3 < x v)) by
      simp only [prepare,localInput,HighGirthStartup.input,HighGirthSetup.K,HighGirthSelection.candidates,
        HighGirthSetup.c,HighGirthSetup.B,HighGirthSelection.branch,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.card_neighborFinset_eq_degree]
      rfl]
  rw [←Bool.decide_and,←Bool.decide_and]
  apply Bool.decide_congr
  have hk : v ∈ HighGirthSetup.B G → v ∈ HighGirthSetup.K G := fun hv => HighGirthSetup.branch_candidates G hv
  simp only [first,HighGirthSetup.I,HighGirthSetup.input,Finset.mem_filter]
  tauto

theorem rounding_run_eq {ids : ℕ} (codec : BitCode V ids) (x : V → ℝ)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (rounding codec).runEncoded G (localInput G x) = fun v =>
      decide (v ∈ HighGirthSetup.F G ∪ HighGirthSetup.selected G
        x labels hfree) := by
  classical
  let s := fun v => prepare (G.neighborFinset v) (localInput G x v)
  have hr := HighGirthProtocol.run_eq G x
    labels hfree s codec (candidate_correct G x) (demand_correct G x)
    (first_correct G x labels hfree) (linked_correct G x) hmono
  simp only [Program.runEncoded_eq_run] at hr ⊢
  change (fun v => ((ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec)).run G
    (fun u => (s u,decide (u ∈ HighGirthSetup.F G))) v).1 ||
      ((ProgramMemory.carry (X := Bool) (HighGirthProtocol.program codec)).run G
    (fun u => (s u,decide (u ∈ HighGirthSetup.F G))) v).2) = _
  rw [ProgramMemory.run]
  change (fun v => (HighGirthProtocol.program codec).run G s v || decide (v ∈ HighGirthSetup.F G)) = _
  change (HighGirthProtocol.program codec).run G s = _ at hr
  rw [hr]
  funext v
  simp only [Finset.mem_union,Bool.decide_or]
  exact Bool.or_comm _ _

#print axioms Paper.TotalDomination.HighGirthVectorRounding.rounding_run_eq

noncomputable def program {ids : ℕ} (codec : BitCode V ids) : Program V ℝ Bool :=
  .seq (.local fun _ _ value => (PUnit.unit,value))
    (.seq (ProgramMemory.carry (X := ℝ) HighGirthStartup.program)
      (.seq (.local fun _ _ s => (⟨s.1,s.2⟩ : Input V)) (rounding codec)))
theorem rounds {ids : ℕ} (codec : BitCode V ids) : (program codec).rounds=9 := by
  simp only [program,Program.rounds,ProgramMemory.rounds,HighGirthStartup.rounds,rounding_rounds]
theorem maxBits {ids : ℕ} (codec : BitCode V ids) : (program codec).maxBits ≤ ids+1 := by
  simp only [program,Program.maxBits,ProgramMemory.maxBits,HighGirthStartup.maxBits,Nat.zero_max]
  exact max_le (by omega) (rounding_maxBits codec)
theorem run_eq {ids : ℕ} (codec : BitCode V ids) (x : V → ℝ)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (program codec).runEncoded G x = fun v =>
      decide (v ∈ HighGirthSetup.F G ∪ HighGirthSetup.selected G x labels hfree) := by
  simp only [program,Program.runEncoded_eq_run,Program.run,ProgramMemory.run]
  rw [HighGirthStartup.correct]
  change (rounding codec).run G (localInput G x) = _
  simpa only [Program.runEncoded_eq_run] using rounding_run_eq G codec x labels hmono hfree
noncomputable def output {ids : ℕ} (codec : BitCode V ids) (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => (program codec).runEncoded G x v

theorem outcome {ids : ℕ} (codec : BitCode V ids) (x : V → ℝ)
    (labels : V → ℕ) (hmono : StrictMono labels)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) (a : ℚ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G (a:ℝ))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (HighGirthSetup.Z G) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ HighGirthSetup.K G, x v=0)
    (hsolver : objective G (HighGirthSetup.I G x labels hfree) (fun v => (HighGirthSetup.c G v:ℝ)) ≤
      (1+(HighGirthSlackArithmetic.rationalAccuracy a:ℝ))*HighGirthSelection.residualOptimum G) :
    (∀ r, ∃ v ∈ output G codec x, G.Adj r v) ∧
    ((output G codec x).card:ℝ) ≤ 2*HighGirthSelection.totalFractionalNumber G ∧
    (program codec).rounds=9 ∧ (program codec).maxBits ≤ ids+1 := by
  have hhiR : (a:ℝ) < ((9/8:ℚ):ℝ) := Rat.cast_lt.mpr hhi
  norm_num at hhiR
  have hs := HighGirthSetup.coefficient_two G x labels hfree (a:ℝ) (by exact_mod_cast ha) hhiR
    hden hx hcap hsupport (by rwa [←HighGirthSlackArithmetic.rational_accuracy_cast])
  have he : output G codec x = HighGirthSetup.F G ∪ HighGirthSetup.selected G x labels hfree := by
    unfold output
    rw [run_eq G codec x labels hmono hfree]
    ext v
    simp
  rw [he]
  exact ⟨hs.1,hs.2,rounds codec,maxBits codec⟩

end Paper.TotalDomination.HighGirthVectorRounding
#print axioms Paper.TotalDomination.HighGirthVectorRounding.outcome
