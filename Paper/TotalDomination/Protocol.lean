import Paper.TotalDomination.Rounding
import Paper.Solver.LocalSearch.GeneralCoveringRequests

/-! Four physical broadcasts implement the total-domination selection.
Input consists of private candidate/demand bits and the vertex's own local
threshold decision. Labels are ordered identifiers, as in the existing
request protocol. No graph or global set is an executable parameter. -/

namespace Paper.TotalDomination.Protocol

open BroadcastModel SevenFoundation

variable {V : Type} [LinearOrder V]

structure Input where
  candidate : Bool
  demand : Bool
  first : Bool

structure ResidualState where
  input : Input
  residual : Bool

structure HighState where
  input : Input
  residual : Bool
  high : Bool

/-- Omit the sender itself when reconstructing an open neighborhood. -/
def near (v : V) (N : Finset V) (msg : N → Bool) : Finset V :=
  FlagNeighborhood.selected v N false msg

def residualRound : Round V Input ResidualState Bool where
  send _ _ s := s.first
  update v N s msg := ⟨s, s.demand && decide (near v N msg = ∅)⟩

def highRound (cutoff : ℕ) : Round V ResidualState HighState Bool where
  send _ _ s := s.residual
  update v N s msg :=
    ⟨s.input, s.residual, s.input.candidate && !s.input.first &&
      decide (cutoff ≤ (near v N msg).card)⟩

def prepareRound : Round V HighState (GeneralCoveringRequests.Input V) Bool where
  send _ _ s := s.high
  update v N s msg :=
    ⟨s.input.first || s.high, s.residual && decide (near v N msg = ∅), s.input.demand, N⟩

def program {b : ℕ} (ids : BitCode V b) (cutoff : ℕ) : Program V Input Bool :=
  .seq (.broadcast 1 BitCode.bool residualRound)
    (.seq (.broadcast 1 BitCode.bool (highRound cutoff))
      (.seq (.broadcast 1 BitCode.bool prepareRound)
        (.seq (.broadcast (b + 1) ids.option GeneralCoveringRequests.selectRound)
          (.local fun _ _ s => s.selected))))

theorem rounds {b : ℕ} (ids : BitCode V b) (cutoff : ℕ) :
    (program ids cutoff).rounds = 4 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) (cutoff : ℕ) :
    (program ids cutoff).maxBits ≤ b + 1 := by
  change max 1 (max 1 (max 1 (max (b + 1) 0))) ≤ b + 1
  omega

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (cutoff N c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program ids cutoff).maxBits ≤ (c + 1) * Nat.clog 2 (N + 2) :=
  (maxBits ids cutoff).trans (logarithmic_message_budget N b c hids).1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem near_correct (S : Finset V) (v : V) :
    near v (G.neighborFinset v) (fun u => decide (u.val ∈ S)) =
      G.neighborFinset v ∩ S := by
  ext u
  simp only [near, FlagNeighborhood.selected, Bool.false_eq_true, if_false,
    Finset.empty_union, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
    true_and, decide_eq_true_eq, Finset.mem_inter]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hn, hs⟩
    exact ⟨⟨u, hn⟩, hs, rfl⟩

theorem near_empty_iff (S : Finset V) (v : V) :
    G.neighborFinset v ∩ S = ∅ ↔ v ∉ TotalDomination.neighbors G S := by
  have he : (G.neighborFinset v ∩ S).Nonempty ↔ v ∈ TotalDomination.neighbors G S := by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨hn, hs⟩ := Finset.mem_inter.mp hu
      exact (TotalDomination.mem_neighbors G).mpr ⟨u, hs, (G.mem_neighborFinset v u).mp hn⟩
    · intro hv
      obtain ⟨u, hs, ha⟩ := (TotalDomination.mem_neighbors G).mp hv
      exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr ha, hs⟩⟩
  rw [← Finset.not_nonempty_iff_eq_empty, he]

variable (I : TotalDomination.Input G) (s : V → Input)

local notation "W" => TotalDomination.first G I
local notation "R" => TotalDomination.residual G I
local notation "H" => TotalDomination.high G I
local notation "U" => TotalDomination.last G I

theorem residual_correct
    (hdemand : ∀ v, (s v).demand = decide (v ∈ I.demands))
    (hfirst : ∀ v, (s v).first = decide (v ∈ W)) :
    eval G residualRound s = fun v => ⟨s v, decide (v ∈ R)⟩ := by
  funext v
  change ResidualState.mk (s v) ((s v).demand && decide (near v
    (G.neighborFinset v) (fun u => (s u.val).first) = ∅)) = _
  apply congrArg (ResidualState.mk (s v))
  simp_rw [hfirst]
  rw [hdemand, near_correct]
  simp only [near_empty_iff, TotalDomination.residual, Finset.mem_sdiff, Bool.decide_and]

theorem high_correct
    (hcandidate : ∀ v, (s v).candidate = decide (v ∈ I.candidates))
    (hfirst : ∀ v, (s v).first = decide (v ∈ W)) :
    eval G (highRound I.cutoff) (fun v => ⟨s v, decide (v ∈ R)⟩) =
      fun v => ⟨s v, decide (v ∈ R), decide (v ∈ H)⟩ := by
  funext v
  change HighState.mk (s v) (decide (v ∈ R))
    ((s v).candidate && !(s v).first && decide (I.cutoff ≤
      (near v (G.neighborFinset v) (fun u => decide (u.val ∈ R))).card)) = _
  apply congrArg (HighState.mk (s v) (decide (v ∈ R)))
  rw [hcandidate, hfirst, near_correct]
  simp only [TotalDomination.high, TotalDomination.hits, Finset.mem_filter,
    Finset.mem_sdiff, Bool.decide_and, decide_not]

theorem prepare_correct
    (hdemand : ∀ v, (s v).demand = decide (v ∈ I.demands))
    (hfirst : ∀ v, (s v).first = decide (v ∈ W)) :
    eval G prepareRound (fun v => ⟨s v, decide (v ∈ R), decide (v ∈ H)⟩) =
      fun v => ⟨decide (v ∈ W ∪ H), decide (v ∈ U), decide (v ∈ I.demands),
        G.neighborFinset v⟩ := by
  funext v
  have hnear := near_correct G H v
  change GeneralCoveringRequests.Input.mk
    ((s v).first || decide (v ∈ H))
    (decide (v ∈ R) && decide (near v (G.neighborFinset v)
      (fun u => decide (u.val ∈ H)) = ∅)) (s v).demand _ = _
  rw [hfirst, hdemand, hnear]
  simp only [near_empty_iff]
  have hlast : (decide (v ∈ R) && decide (v ∉ TotalDomination.neighbors G H)) =
      decide (v ∈ U) := by
    rw [← Bool.decide_and]
    apply Bool.decide_congr
    simp only [TotalDomination.last, TotalDomination.served, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hlast]
  simp only [Finset.mem_union, Bool.decide_or]

/-- Mathematical IDs agree with the order of the labels used by the runtime.
The ID function is proof-side data, never an executable global argument. -/
theorem minimum_eq_request (hmono : StrictMono I.identifier) (r : V) :
    MaskedMinimum.minimum (G.neighborFinset r) = some (TotalDomination.request G I r) := by
  have hmem := (G.mem_neighborFinset r _).mpr (TotalDomination.request_adj G I r)
  obtain ⟨u, hu, hmin⟩ := MaskedMinimum.minimum_le hmem
  have hcost := TotalDomination.request_identifier_le G I r u
    ((G.mem_neighborFinset r u).mp (MaskedMinimum.minimum_mem hu))
  have hreverse : TotalDomination.request G I r ≤ u := by
    by_contra hn
    have hs := hmono (lt_of_not_ge hn)
    exact (not_lt_of_ge hcost) hs
  have he : u = TotalDomination.request G I r := le_antisymm hmin hreverse
  simpa only [he] using hu

theorem requested_eq_image (hmono : StrictMono I.identifier) :
    GeneralCoveringRequests.requested (fun r => G.neighborFinset r) U =
      (U).image (TotalDomination.request G I) := by
  ext v
  rw [GeneralCoveringRequests.mem_requested]
  simp only [minimum_eq_request G I hmono, Option.some.injEq, Finset.mem_image]

/-- Exact encoded execution equals the original mathematical selection.
Only local input bits are related to the specification; no output guarantee
or graphwide datum is supplied as a runtime assumption. -/
theorem run_eq {b : ℕ} (ids : BitCode V b)
    (hcandidate : ∀ v, (s v).candidate = decide (v ∈ I.candidates))
    (hdemand : ∀ v, (s v).demand = decide (v ∈ I.demands))
    (hfirst : ∀ v, (s v).first = decide (v ∈ W))
    (hmono : StrictMono I.identifier) :
    (program ids I.cutoff).runEncoded G s =
      fun v => decide (v ∈ TotalDomination.output G I) := by
  rw [Program.runEncoded_eq_run]
  change (fun v => (eval G GeneralCoveringRequests.selectRound
    (eval G prepareRound (eval G (highRound I.cutoff) (eval G residualRound s))) v).selected) = _
  rw [residual_correct G I s hdemand hfirst, high_correct G I s hcandidate hfirst,
    prepare_correct G I s hdemand hfirst]
  rw [GeneralCoveringRequests.select_correct G (fun r => G.neighborFinset r) (W ∪ H) U
    (fun v => ⟨decide (v ∈ W ∪ H), decide (v ∈ U), decide (v ∈ I.demands), G.neighborFinset v⟩)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by
      intro r _ v hv
      exact (mem_closed G v r).mpr (Or.inr ((G.mem_neighborFinset r v).mp hv)))]
  rw [GeneralCoveringRequests.selectedPlus, requested_eq_image G I hmono]
  rfl

def output {b : ℕ} (ids : BitCode V b) (cutoff : ℕ) (s : V → Input) : Finset V :=
  Finset.univ.filter fun v => (program ids cutoff).runEncoded G s v

theorem output_eq {b : ℕ} (ids : BitCode V b)
    (hcandidate : ∀ v, (s v).candidate = decide (v ∈ I.candidates))
    (hdemand : ∀ v, (s v).demand = decide (v ∈ I.demands))
    (hfirst : ∀ v, (s v).first = decide (v ∈ W)) (hmono : StrictMono I.identifier) :
    output G ids I.cutoff s = TotalDomination.output G I := by
  unfold output
  rw [run_eq G I s ids hcandidate hdemand hfirst hmono]
  ext v
  simp

end Paper.TotalDomination.Protocol

#print axioms Paper.TotalDomination.Protocol.rounds
#print axioms Paper.TotalDomination.Protocol.maxBits
#print axioms Paper.TotalDomination.Protocol.run_eq
#print axioms Paper.TotalDomination.Protocol.output_eq
