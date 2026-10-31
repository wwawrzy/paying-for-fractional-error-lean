import Paper.Partitions.Local.DeterministicColorReductionIdentifiers
import Paper.Communication.BoundedGossip
import Paper.Communication.ProgramMemory
import Paper.Partitions.Local.NeighborBallGraph

/-! One real physical simulation of a color-reduction step on a radius-r power.
Singleton tagged colors are flooded using the received bounded gossip program.
The sender's own color is private memory. The final local rule removes its own
identifier and uses only received tagged colors. No power-neighbor oracle or
graph is an argument of the executable program. The power graph below is a
specification, connected to the collected payloads by actual bounded walks. -/
namespace Paper.DeterministicColorReductionPhysicalStep
open BroadcastModel
abbrev Bits := DeterministicColorReductionStep.Bits
abbrev Packet (V : Type) (b : ℕ) := V × Bits b
variable {V : Type} [LinearOrder V]

def packetCode {ids : ℕ} (C : BitCode V ids) (b : ℕ) : BitCode (Packet V b) (ids + b) :=
  PacketCode.product C (DeterministicColorReductionStep.bitsCode b)

def prepare (b : ℕ) : Program V (Bits b) (List (Packet V b) × Bits b) :=
  .local fun v _ s => ([(v, s)], s)

def localPairs (b : ℕ) (v : V) (own : Bits b) (l : List (Packet V b)) :
    Finset (DeterministicColorReductionStep.Pair b) :=
  (l.toFinset.filter (fun p => p.1 ≠ v)).biUnion
    (fun p => DeterministicColorReductionStep.witness own p.2)

def finish (b D : ℕ) : Program V (List (Packet V b) × Bits b)
    (Bits (DeterministicColorReductionCodec.width b D)) :=
  .local fun v _ s => DeterministicColorReductionCodec.encodeOutput b D (localPairs b v s.2 s.1)

def program {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) :
    Program V (Bits b) (Bits (DeterministicColorReductionCodec.width b ((Δ + 1) ^ r))) :=
  .seq (prepare b)
    (.seq (ProgramMemory.carry (X := Bits b) (BoundedGossip.program (packetCode C b) Δ 1 r))
      (finish b ((Δ + 1) ^ r)))

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) :
    (program C Δ r b).rounds = r := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds,
    BoundedGossip.program, Program.iterate_rounds, BoundedGossipRound.program,
    Program.rounds, Nat.mul_one, Nat.zero_add, Nat.add_zero]

theorem gossip_bits {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) :
    (BoundedGossip.program (V := V) (packetCode C b) Δ 1 r).maxBits ≤
      (Δ + 1) ^ r * (ids + b + 1) := by
  simpa only [BoundedGossip.program, BoundedGossipRound.program, Program.maxBits, Nat.one_mul] using
    Program.iterate_maxBits
      (BoundedGossipRound.program (V := V) (packetCode C b) (1 * (Δ + 1) ^ r)) r

theorem maxBits {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) :
    (program C Δ r b).maxBits ≤ (Δ + 1) ^ r * (ids + b + 1) := by
  simpa only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits,
    Nat.zero_max, Nat.max_zero] using gossip_bits C Δ r b

theorem physical_parameters {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) :
    (program C Δ r b).rounds = r ∧
    (program C Δ r b).maxBits ≤ (Δ + 1) ^ r * (ids + b + 1) :=
  ⟨rounds C Δ r b, maxBits C Δ r b⟩

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The loopless radius-r power; it is used in the specification, not the program. -/
def power (r : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u r
  symm := by
    intro u v h
    obtain ⟨p, hp⟩ := (NeighborBallGraph.mem_iff_walk G u v r).mp h.2
    exact ⟨h.1.symm, (NeighborBallGraph.mem_iff_walk G v u r).mpr
      ⟨p.reverse, by simpa only [SimpleGraph.Walk.length_reverse] using hp⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance powerDecidable (r : ℕ) : DecidableRel (power G r).Adj :=
  fun u v => inferInstanceAs (Decidable
    (u ≠ v ∧ v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u r))

theorem power_neighbor_mem (r : ℕ) (u v : V) :
    v ∈ (power G r).neighborFinset u ↔
      u ≠ v ∧ v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u r :=
  (power G r).mem_neighborFinset u v

theorem power_degree_bound (Δ r : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (power G r).degree v ≤ (Δ + 1) ^ r := by
  change ((power G r).neighborFinset v).card ≤ (Δ + 1) ^ r
  calc
    _ ≤ (NeighborBalls.ball (fun w => G.neighborFinset w) v r).card :=
      Finset.card_le_card (fun u hu => ((power_neighbor_mem G r v u).mp hu).2)
    _ ≤ _ := NeighborBallGraph.graph_card_bound G Δ hdeg v r

/-- Exactly the tagged initial colors within the closed physical walk radius. -/
theorem knowledge_mem (r b : ℕ) (c : V → Bits b) (v : V) (a : Packet V b) :
    a ∈ GossipKnowledge.knowledge G (fun u => {(u, c u)}) r v ↔
      a.1 ∈ NeighborBalls.ball (fun w => G.neighborFinset w) v r ∧ a.2 = c a.1 := by
  constructor
  · intro ha
    obtain ⟨u, p, hp, hau⟩ :=
      GossipKnowledge.exists_walk G (fun u => {(u, c u)}) r v ha
    have he : a = (u, c u) := Finset.mem_singleton.mp hau
    subst a
    exact ⟨NeighborBallGraph.walk_mem G p r hp, rfl⟩
  · rintro ⟨ha, hc⟩
    obtain ⟨p, hp⟩ := (NeighborBallGraph.mem_iff_walk G v a.1 r).mp ha
    apply GossipKnowledge.of_walk G (fun u => {(u, c u)}) p r hp
    exact Finset.mem_singleton.mpr (Prod.ext rfl hc)

theorem gathered {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) (c : V → Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    ((BoundedGossip.program (packetCode C b) Δ 1 r).run G (fun u => [(u, c u)]) v).toFinset =
      GossipKnowledge.knowledge G (fun u => {(u, c u)}) r v := by
  have h := BoundedGossip.correct G (packetCode C b) Δ 1 r (fun u => [(u, c u)]) hdeg
    (by intro u; simp) (by intro u; simp)
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using h.1 v

theorem localPairs_eq (r b : ℕ) (c : V → Bits b) (v : V) (l : List (Packet V b))
    (hl : l.toFinset = GossipKnowledge.knowledge G (fun u => {(u, c u)}) r v) :
    localPairs b v (c v) l =
      DeterministicColorReductionStep.output (fun u => (power G r).neighborFinset u) c v := by
  unfold localPairs DeterministicColorReductionStep.output
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hal, hne⟩ := Finset.mem_filter.mp ha
    have hak : a ∈ GossipKnowledge.knowledge G (fun u => {(u, c u)}) r v := hl ▸ hal
    obtain ⟨hball, hc⟩ := (knowledge_mem G r b c v a).mp hak
    refine Finset.mem_biUnion.mpr ⟨a.1, (power_neighbor_mem G r v a.1).mpr
      ⟨hne.symm, hball⟩, ?_⟩
    simpa only [hc] using hp
  · intro hp
    obtain ⟨u, hu, hp⟩ := Finset.mem_biUnion.mp hp
    have hnear := (power_neighbor_mem G r v u).mp hu
    have hak : (u, c u) ∈ GossipKnowledge.knowledge G (fun u => {(u, c u)}) r v :=
      (knowledge_mem G r b c v (u, c u)).mpr ⟨hnear.2, rfl⟩
    have hal : (u, c u) ∈ l.toFinset := hl.symm ▸ hak
    exact Finset.mem_biUnion.mpr ⟨(u, c u), Finset.mem_filter.mpr ⟨hal, hnear.1.symm⟩, hp⟩

/-- Full encoded physical output equals the accepted local rule on the power. -/
theorem correct {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) (c : V → Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program C Δ r b).runEncoded G c v =
      DeterministicColorReductionCodec.nextColor b ((Δ + 1) ^ r)
        (fun u => (power G r).neighborFinset u) c v := by
  rw [Program.runEncoded_eq_run]
  simp only [program, prepare, finish, Program.run, ProgramMemory.run]
  change DeterministicColorReductionCodec.encodeOutput b ((Δ + 1) ^ r)
      (localPairs b v (c v)
        ((BoundedGossip.program (packetCode C b) Δ 1 r).run G (fun u => [(u, c u)]) v)) = _
  unfold DeterministicColorReductionCodec.nextColor
  exact congrArg (DeterministicColorReductionCodec.encodeOutput b ((Δ + 1) ^ r))
    (localPairs_eq G r b c v _ (gathered G C Δ r b c hdeg v))

theorem proper {ids : ℕ} (C : BitCode V ids) (Δ r b : ℕ) (c : V → Bits b)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hc : ∀ u v, (power G r).Adj u v → c u ≠ c v)
    (u v : V) (ha : (power G r).Adj u v) :
    (program C Δ r b).runEncoded G c u ≠ (program C Δ r b).runEncoded G c v := by
  have hn : DeterministicColorReductionCodec.nextColor b ((Δ + 1) ^ r)
        (fun w => (power G r).neighborFinset w) c u ≠
      DeterministicColorReductionCodec.nextColor b ((Δ + 1) ^ r)
        (fun w => (power G r).neighborFinset w) c v := by
    simpa only [DeterministicColorReductionCodec.correct] using
      DeterministicColorReductionCodec.proper (power G r) b ((Δ + 1) ^ r) c
        (power_degree_bound G Δ r hdeg) hc u v ha
  simpa only [correct G C Δ r b c hdeg] using hn

end Graph
end Paper.DeterministicColorReductionPhysicalStep

#print axioms Paper.DeterministicColorReductionPhysicalStep.knowledge_mem
#print axioms Paper.DeterministicColorReductionPhysicalStep.gathered
#print axioms Paper.DeterministicColorReductionPhysicalStep.power_degree_bound
#print axioms Paper.DeterministicColorReductionPhysicalStep.localPairs_eq
#print axioms Paper.DeterministicColorReductionPhysicalStep.correct
#print axioms Paper.DeterministicColorReductionPhysicalStep.proper
#print axioms Paper.DeterministicColorReductionPhysicalStep.physical_parameters
