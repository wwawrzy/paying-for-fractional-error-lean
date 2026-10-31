import Paper.Partitions.Local.DeterministicPartitionIterationPower
import Paper.Communication.ProgramMemory

/-! The actual T-stage broadcast program. Private saved parts are carried
through each received stage without changing its messages or codecs. All
vertices keep relaying after acceptance. Only terminal active vertices add
a singleton. Supplied vertex colors are retained, never computed here. -/
namespace Paper.DeterministicPartitionIterationProgram
open BroadcastModel
variable {V : Type} [LinearOrder V]

@[ext] structure State (V : Type) (Φ : ℕ) where
  active : Bool
  color : Fin Φ
  saved : Finset V

def update {Φ : ℕ} (s : State V Φ) (U : Finset V) : State V Φ :=
  ⟨s.active && decide (U = ∅), s.color, s.saved ∪ U⟩

def prepare (Φ : ℕ) : Program V (State V Φ) (DeterministicPartitionBroadcast.Input Φ × State V Φ) :=
  .local fun _ _ s => ((s.active, s.color), s)

def finishStage (Φ : ℕ) : Program V (Finset V × State V Φ) (State V Φ) :=
  .local fun _ _ s => update s.2 s.1

def stage {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    Program V (State V Φ) (State V Φ) :=
  .seq (prepare Φ)
    (.seq (ProgramMemory.carry (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ)) (finishStage Φ))

def steps {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    ℕ → Program V (State V Φ) (State V Φ)
  | 0 => .local fun _ _ s => s
  | n + 1 => .seq (stage C Δ k t Φ q hΦ) (steps C Δ k t Φ q hΦ n)

def initState (Φ : ℕ) : Program V (DeterministicPartitionBroadcast.Input Φ) (State V Φ) :=
  .local fun _ _ s => ⟨s.1, s.2, ∅⟩

def finish (Φ : ℕ) : Program V (State V Φ) (Finset V) :=
  .local fun v _ s => s.saved ∪ if s.active = true then {v} else ∅

def program {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q T : ℕ) (hΦ : 0 < Φ) :
    Program V (DeterministicPartitionBroadcast.Input Φ) (Finset V) :=
  .seq (initState Φ) (.seq (steps C Δ k t Φ q hΦ T) (finish Φ))

/-- Labels of actual finite part families, without a choice of a part. -/
def rootLabel (P : Finset (Finset V)) (v : V) : Finset V :=
  P.biUnion (fun U => if v ∈ U then U else ∅)

theorem mem_rootLabel (P : Finset (Finset V)) (v w : V) :
    w ∈ rootLabel P v ↔ ∃ U ∈ P, v ∈ U ∧ w ∈ U := by
  constructor
  · intro hw
    obtain ⟨U, hU, hw⟩ := Finset.mem_biUnion.mp hw
    split_ifs at hw with hv
    · exact ⟨U, hU, hv, hw⟩
    · exact False.elim (Finset.notMem_empty w hw)
  · rintro ⟨U, hU, hv, hw⟩
    exact Finset.mem_biUnion.mpr ⟨U, hU, by simpa only [if_pos hv] using hw⟩

theorem rootLabel_union (P Q : Finset (Finset V)) (v : V) :
    rootLabel (P ∪ Q) v = rootLabel P v ∪ rootLabel Q v := by
  simp only [rootLabel, Finset.union_biUnion]

theorem rootLabel_singletons (S : Finset V) (v : V) :
    rootLabel (S.image (fun u => {u})) v = if v ∈ S then {v} else ∅ := by
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    ext w
    rw [mem_rootLabel]
    constructor
    · rintro ⟨U, hU, hvU, hwU⟩
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hU
      exact Finset.mem_singleton.mpr
        ((Finset.mem_singleton.mp hwU).trans (Finset.mem_singleton.mp hvU).symm)
    · intro hw
      exact ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_singleton_self v, hw⟩
  · rw [if_neg hv]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨U, hU, hvU, _⟩ := (mem_rootLabel _ v w).mp hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
    exact hv ((Finset.mem_singleton.mp hvU).symm ▸ hu)

theorem rootLabel_of_mem (P : Finset (Finset V))
    (hd : (P : Set (Finset V)).Pairwise Disjoint) (U : Finset V)
    (hU : U ∈ P) (v : V) (hv : v ∈ U) : rootLabel P v = U := by
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨W, hW, hvW, hwW⟩ := (mem_rootLabel P v w).mp hw
    have he : W = U := by
      by_contra hn
      exact Finset.disjoint_left.mp (hd hW hU hn) hvW hv
    simpa only [he] using hwW
  · intro w hw
    exact (mem_rootLabel P v w).mpr ⟨U, hU, hv, hw⟩

theorem part_eq_rootLabel (E : Finset (Finset V)) (color : Finset V → ℕ) (q : ℕ) (v : V) :
    DeterministicPartitionLocality.part E color q v = rootLabel (DeterministicPartitionGreedy.run E color q) v := by
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨U, hU, hwU⟩ := Finset.mem_biUnion.mp hw
    have hh := Finset.mem_filter.mp hU
    exact (mem_rootLabel _ v w).mpr ⟨U, hh.1, hh.2, hwU⟩
  · intro w hw
    obtain ⟨U, hU, hvU, hwU⟩ := (mem_rootLabel _ v w).mp hw
    exact Finset.mem_biUnion.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hvU⟩, hwU⟩

theorem part_empty_iff (E : Finset (Finset V)) (color : Finset V → ℕ) (q : ℕ) (v : V) :
    DeterministicPartitionLocality.part E color q v = ∅ ↔
      v ∉ DeterministicPartitionGreedy.removed E color q := by
  rw [part_eq_rootLabel]
  constructor
  · intro he hv
    obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
    have hh := (mem_rootLabel _ v v).mpr ⟨U, hU, hvU, hvU⟩
    rw [he] at hh
    exact Finset.notMem_empty v hh
  · intro hv
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨U, hU, hvU, _⟩ := (mem_rootLabel _ v w).mp hw
    exact hv (Finset.mem_biUnion.mpr ⟨U, hU, hvU⟩)

def stagePart (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (v : V) : Finset V :=
  DeterministicPartitionLocality.part (FiniteEligibility.family N S k t) color q v

theorem next_iff (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (v : V) :
    v ∈ DeterministicPartitionProgress.next N S k t color q ↔
      v ∈ S ∧ stagePart N k t color q S v = ∅ := by
  simp only [DeterministicPartitionProgress.next, Finset.mem_sdiff, stagePart, part_empty_iff,
    DeterministicPartitionProgress.removed, DeterministicPartitionProgress.accepted,
    DeterministicPartitionGreedy.removed]

theorem stagePart_outside (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (v : V) (hv : v ∉ S) : stagePart N k t color q S v = ∅ := by
  apply (part_empty_iff _ color q v).mpr
  intro hr
  exact hv (DeterministicPartitionProgress.removed_subset N S k t color q hr)

def acceptedLabel (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (T : ℕ) (v : V) : Finset V :=
  rootLabel (DeterministicPartitionIterationCore.run N k t color q S T).accepted v

theorem acceptedLabel_succ (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (n : ℕ) (v : V) :
    acceptedLabel N k t color q S (n + 1) v = stagePart N k t color q S v ∪
      acceptedLabel N k t color q (DeterministicPartitionProgress.next N S k t color q) n v := by
  unfold acceptedLabel
  rw [DeterministicPartitionIterationCore.accepted_succ, rootLabel_union]
  rw [stagePart, part_eq_rootLabel, DeterministicPartitionProgress.accepted]

theorem label_parts (N : V → Finset V) (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (S : Finset V) (T : ℕ) (v : V) :
    rootLabel (DeterministicPartitionIterationCore.parts N k t color q S T) v =
      acceptedLabel N k t color q S T v ∪
        if v ∈ (DeterministicPartitionIterationCore.run N k t color q S T).remaining then {v} else ∅ := by
  unfold DeterministicPartitionIterationCore.parts
  rw [rootLabel_union, rootLabel_singletons]
  rfl

/-- Canonical semantic state; only proofs use the global set S. -/
def state {Φ : ℕ} (S : Finset V) (χ : V → Fin Φ) (saved : V → Finset V) : V → State V Φ :=
  fun v => ⟨decide (v ∈ S), χ v, saved v⟩

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_stage_raw {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (s : V → State V Φ) :
    (stage C Δ k t Φ q hΦ).run G s = fun v => update (s v)
      ((DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).run G
        (fun u => ((s u).active, (s u).color)) v) := by
  change (finishStage Φ).run G ((ProgramMemory.carry
    (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ)).run G
      (fun v => (((s v).active, (s v).color), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_stage {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (χ : V → Fin Φ) (saved : V → Finset V) :
    (stage C Δ k t Φ q hΦ).run G (state S χ saved) =
      state (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t
        (DeterministicPartitionIterationPower.color (fun v => G.neighborFinset v) Δ k Φ χ) q)
        χ (fun v => saved v ∪ stagePart (fun v => G.neighborFinset v) k t
          (DeterministicPartitionIterationPower.color (fun v => G.neighborFinset v) Δ k Φ χ) q S v) := by
  have hp : (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).run G
      (fun u => (decide (u ∈ S), χ u)) = fun v =>
        stagePart (fun u => G.neighborFinset u) k t
          (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S v := by
    funext v
    simpa only [Program.runEncoded_eq_run] using
      DeterministicPartitionIterationPower.stage_output G C Δ k t Φ q hΦ S χ hdeg v
  rw [run_stage_raw]
  change (fun v => update (state S χ saved v)
    ((DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).run G
      (fun u => (decide (u ∈ S), χ u)) v)) = _
  rw [hp]
  funext v
  apply State.ext
  · change (decide (v ∈ S) && decide (stagePart (fun u => G.neighborFinset u) k t
      (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S v = ∅)) =
        decide (v ∈ DeterministicPartitionProgress.next (fun u => G.neighborFinset u) S k t
          (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact (next_iff _ k t _ q S v).symm
  · rfl
  · rfl

/-- A vertex accepted earlier keeps its private complete part unchanged. -/
theorem run_stage_inactive_saved {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (χ : V → Fin Φ) (saved : V → Finset V)
    (v : V) (hv : v ∉ S) :
    ((stage C Δ k t Φ q hΦ).run G (state S χ saved) v).saved = saved v := by
  rw [run_stage G C Δ k t Φ q hΦ hdeg S χ saved]
  change saved v ∪ stagePart (fun u => G.neighborFinset u) k t
    (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S v = saved v
  rw [stagePart_outside _ k t _ q S v hv, Finset.union_empty]

/-- Exact full state after T actual stages, for arbitrary saved local data. -/
theorem run_steps {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (T : ℕ) (S : Finset V) (χ : V → Fin Φ) (saved : V → Finset V) :
    (steps C Δ k t Φ q hΦ T).run G (state S χ saved) =
      state (DeterministicPartitionIterationCore.run (fun v => G.neighborFinset v) k t
        (DeterministicPartitionIterationPower.color (fun v => G.neighborFinset v) Δ k Φ χ) q S T).remaining
        χ (fun v => saved v ∪ acceptedLabel (fun v => G.neighborFinset v) k t
          (DeterministicPartitionIterationPower.color (fun v => G.neighborFinset v) Δ k Φ χ) q S T v) := by
  induction T generalizing S saved with
  | zero => simp only [steps, Program.run, DeterministicPartitionIterationCore.run,
      acceptedLabel, rootLabel, Finset.biUnion_empty, Finset.union_empty]
  | succ n ih =>
    change (steps C Δ k t Φ q hΦ n).run G ((stage C Δ k t Φ q hΦ).run G (state S χ saved)) = _
    rw [run_stage G C Δ k t Φ q hΦ hdeg S χ saved, ih]
    simp only [DeterministicPartitionIterationCore.remaining_succ, acceptedLabel_succ, Finset.union_assoc]

/-- Decoded execution agrees with the complete identifier set of Core.parts. -/
theorem correct {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q T : ℕ) (hΦ : 0 < Φ)
    (S : Finset V) (χ : V → Fin Φ) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program C Δ k t Φ q T hΦ).runEncoded G (fun u => (decide (u ∈ S), χ u)) v =
      (DeterministicPartitionIterationCore.parts (fun u => G.neighborFinset u) k t
        (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S T).biUnion
          (fun U => if v ∈ U then U else ∅) := by
  rw [Program.runEncoded_eq_run]
  change (finish Φ).run G ((steps C Δ k t Φ q hΦ T).run G (state S χ (fun _ => ∅))) v = _
  rw [run_steps G C Δ k t Φ q hΦ hdeg T S χ]
  change ((∅ : Finset V) ∪ acceptedLabel (fun u => G.neighborFinset u) k t
      (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S T v) ∪
    (if decide (v ∈ (DeterministicPartitionIterationCore.run (fun u => G.neighborFinset u) k t
      (DeterministicPartitionIterationPower.color (fun u => G.neighborFinset u) Δ k Φ χ) q S T).remaining) = true
      then {v} else ∅) = rootLabel _ v
  rw [label_parts]
  simp only [Finset.empty_union, decide_eq_true_eq]

theorem output_part {ids : ℕ} (C : BitCode V ids) (Δ k t Φ T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hΦ : 0 < Φ) (S : Finset V) (χ : V → Fin Φ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (v : V) (hv : v ∈ S) :
    let U := (program C Δ k t Φ (Φ * 2 ^ ((Δ + 1) ^ k)) T hΦ).runEncoded G
      (fun u => (decide (u ∈ S), χ u)) v
    U ∈ (DeterministicPartitionIterationPower.partition G Δ hdeg k hk t ht Φ χ hpower S T).parts ∧
      v ∈ U ∧ U.card ≤ k ∧ (G.induce (U : Set V)).Connected := by
  let P := DeterministicPartitionIterationPower.partition G Δ hdeg k hk t ht Φ χ hpower S T
  obtain ⟨U, hU, hvU⟩ := P.covers v hv
  have hlabel : rootLabel P.parts v = U := rootLabel_of_mem P.parts P.disjoint U hU v hvU
  have he : (program C Δ k t Φ (Φ * 2 ^ ((Δ + 1) ^ k)) T hΦ).runEncoded G
      (fun u => (decide (u ∈ S), χ u)) v = U := by
    rw [correct G C Δ k t Φ (Φ * 2 ^ ((Δ + 1) ^ k)) T hΦ S χ hdeg v]
    change rootLabel _ v = U
    rw [← DeterministicPartitionIterationPower.partition_parts G Δ hdeg k hk t ht Φ χ hpower S T]
    exact hlabel
  dsimp only
  rw [he]
  exact ⟨hU, hvU, P.size U hU, P.connected U hU⟩

end Graph

theorem stage_rounds {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    (stage C Δ k t Φ q hΦ).rounds = q * k + 2 * k + 1 := by
  letI : Fintype V := Fintype.ofInjective C.encode C.injective
  simp only [stage, prepare, finishStage, Program.rounds, ProgramMemory.rounds,
    Nat.zero_add, Nat.add_zero]
  exact DeterministicPartitionBroadcast.rounds C Δ k t Φ q hΦ

theorem stage_maxBits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    (stage C Δ k t Φ q hΦ).maxBits = (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).maxBits := by
  simp only [stage, prepare, finishStage, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]

theorem steps_rounds {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) (T : ℕ) :
    (steps C Δ k t Φ q hΦ T).rounds = T * (q * k + 2 * k + 1) := by
  induction T with
  | zero => simp only [steps, Program.rounds, Nat.zero_mul]
  | succ n ih =>
    simp only [steps, Program.rounds, stage_rounds, ih, Nat.succ_mul]
    omega

theorem steps_maxBits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) (T : ℕ) :
    (steps C Δ k t Φ q hΦ T).maxBits ≤ (DeterministicPartitionBroadcast.program C Δ k t Φ q hΦ).maxBits := by
  induction T with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [steps, Program.maxBits, stage_maxBits]
    exact max_le (le_refl _) ih

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q T : ℕ) (hΦ : 0 < Φ) :
    (program C Δ k t Φ q T hΦ).rounds = T * (q * k + 2 * k + 1) := by
  simp only [program, initState, finish, Program.rounds, steps_rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q T : ℕ) (hΦ : 0 < Φ) :
    (program C Δ k t Φ q T hΦ).maxBits ≤
      (Δ + 1) ^ (q * k + 2 * k + 1) * (ids + (Δ * (ids + 1) + (1 + Φ)) + 1) := by
  letI : Fintype V := Fintype.ofInjective C.encode C.injective
  apply le_trans _ (DeterministicPartitionBroadcast.maxBits C Δ k t Φ q hΦ)
  simp only [program, initState, finish, Program.maxBits, Nat.zero_max, Nat.max_zero]
  exact steps_maxBits C Δ k t Φ q hΦ T

theorem logarithmic_bits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q T : ℕ) (hΦ : 0 < Φ)
    (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (program C Δ k t Φ q T hΦ).maxBits ≤
      ((Δ + 1) ^ (q * k + 2 * k + 1) * (Δ + Φ + 3) * (c + 1)) * Nat.clog 2 (N + 2) := by
  letI : Fintype V := Fintype.ofInjective C.encode C.injective
  apply le_trans _ (DeterministicPartitionBroadcast.logarithmic_bits C Δ k t Φ q hΦ N c hids)
  simp only [program, initState, finish, Program.maxBits, Nat.zero_max, Nat.max_zero]
  exact steps_maxBits C Δ k t Φ q hΦ T

end Paper.DeterministicPartitionIterationProgram

#print axioms Paper.DeterministicPartitionIterationProgram.run_steps
#print axioms Paper.DeterministicPartitionIterationProgram.correct
#print axioms Paper.DeterministicPartitionIterationProgram.output_part
#print axioms Paper.DeterministicPartitionIterationProgram.rounds
#print axioms Paper.DeterministicPartitionIterationProgram.logarithmic_bits
