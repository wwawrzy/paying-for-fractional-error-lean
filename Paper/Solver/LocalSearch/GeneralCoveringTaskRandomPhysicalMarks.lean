import Paper.Partitions.Local.ActiveFiniteBitPartition
import Paper.Solver.LocalSearch.GeneralCoveringTaskPhysicalMarks

/-! One physical preparation, then the actual active random partition translated
on its learned low graph. Original cost/own coins remain private memory. Every
outcome supplies canonical fields for task cores; no expectation transport or
randomized approximation endpoint is asserted here. -/
namespace Paper.GeneralCoveringTaskRandomPhysicalMarks
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

abbrev Coins := ActiveFiniteBitPartition.Bits
abbrev Saved (B Δ k b n : ℕ) := Fin (B + 1) × Coins Δ k b n
abbrev Input (V : Type) (B Δ k b n : ℕ) := GeneralCoveringOwners.Input V × Saved B Δ k b n

structure Output (V : Type) (B Δ k b n : ℕ) where
  fields : GeneralCoveringTaskRoles.Fields V B
  label : Finset V
  boundary : Bool
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  coins : Coins Δ k b n

def initState (B Δ k b n : ℕ) :
    Program V (GeneralCoveringOwnerVirtualPrepare.Env V × Saved B Δ k b n)
      ((ActiveFiniteBitPartition.Input Δ k b n × GeneralCoveringOwnerVirtualPrepare.Env V) × Saved B Δ k b n) :=
  .local (fun _ _ s => (((s.1.low, s.2.2), s.1), s.2))

def finishValue {B Δ k b n : ℕ}
    (s : ((Finset V × Bool) × GeneralCoveringOwnerVirtualPrepare.Env V) × Saved B Δ k b n) : Output V B Δ k b n where
  fields := GeneralCoveringTaskRoles.fromLabel s.2.1 (if s.1.2.low then s.1.1.1 else ∅) (s.1.2.low && !s.1.1.2)
  label := s.1.1.1
  boundary := s.1.1.2
  env := s.1.2
  coins := s.2.2

def finish (B Δ k b n : ℕ) :
    Program V (((Finset V × Bool) × GeneralCoveringOwnerVirtualPrepare.Env V) × Saved B Δ k b n) (Output V B Δ k b n) :=
  .local (fun _ _ s => finishValue s)

/-- Native preparation ONCE; translate is used directly, never execute/fromOwners. -/
def program {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ) :
    Program V (Input V B Δ k b n) (Output V B Δ k b n) :=
  .seq (ProgramMemory.carry (X := Saved B Δ k b n) (GeneralCoveringOwnerVirtualPrepare.program I L Δ))
    (.seq (initState B Δ k b n)
      (.seq (ProgramMemory.carry (X := Saved B Δ k b n)
        (GeneralCoveringOwnerSimulation.translate I L Δ (ActiveFiniteBitPartition.program I Δ k t b n)))
        (finish B Δ k b n)))

variable [Fintype V]

section Public
variable {W : Type} [Fintype W] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)
noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable def publicPartition (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Coins Δ k b n) :
    SmallParts.Data (PublicEmbedding.graph J e) (GeneralCoveringTaskPartitionMarks.activeImage e) k :=
  ActiveFiniteBitPartition.partition (PublicEmbedding.graph J e) Δ k hk t b n
    (GeneralCoveringTaskPartitionMarks.activeImage e) β

noncomputable def pulledPartition (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Coins Δ k b n) :
    SmallParts.Data J Finset.univ k :=
  PublicPartitionPullback.data J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e) (publicPartition J e Δ k hk t b n β)

/-- Exact public full label of the actual pulled random part; no inverse/default vertex. -/
theorem label_image (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Coins Δ k b n) (w : W) :
    (DisjointPartLabels.label (pulledPartition J e Δ k hk t b n β).parts w).image e =
      DisjointPartLabels.label (publicPartition J e Δ k hk t b n β).parts (e w) :=
  GeneralCoveringTaskPartitionMarks.label_image J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e) (publicPartition J e Δ k hk t b n β) w

theorem embedded_output {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (β : V → Coins Δ k b n) (hdeg : ∀ w, J.degree w ≤ Δ)
    (U : Finset W) (hU : U ∈ (pulledPartition J e Δ k hk t b n β).parts) (w : W) (hw : w ∈ U) :
    (ActiveFiniteBitPartition.program I Δ k t b n).runEncoded (PublicEmbedding.graph J e)
      (fun v => (decide (v ∈ GeneralCoveringTaskPartitionMarks.activeImage e), β v)) (e w) =
      (U.image e, decide (w ∈ BoundaryOwners.vertices J Finset.univ (pulledPartition J e Δ k hk t b n β).parts)) := by
  have he := ActiveFiniteBitPartition.correct (PublicEmbedding.graph J e) I Δ k hk t ht b n
    (GeneralCoveringTaskPartitionMarks.activeImage e) β (PublicEmbedding.degree_bound J e Δ hdeg) (e w)
  have hl := GeneralCoveringTaskPartitionMarks.label_part_image J e
    (GeneralCoveringTaskPartitionMarks.activeImage e) k (GeneralCoveringTaskPartitionMarks.activeImage_iff e)
    (publicPartition J e Δ k hk t b n β) U hU w hw
  have hb := PublicPartitionPullback.boundary J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e) (publicPartition J e Δ k hk t b n β) w
  exact he.trans (congrArg₂ Prod.mk hl (Bool.decide_congr hb.symm))
end Public

section Physical
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem prepared_run {B Δ k b n : ℕ}
    (prep : Program V (GeneralCoveringOwners.Input V) (GeneralCoveringOwnerVirtualPrepare.Env V))
    (client : Program V (ActiveFiniteBitPartition.Input Δ k b n × GeneralCoveringOwnerVirtualPrepare.Env V)
      ((Finset V × Bool) × GeneralCoveringOwnerVirtualPrepare.Env V))
    (input : V → GeneralCoveringOwners.Input V) (saved : V → Saved B Δ k b n) :
    (Program.seq (ProgramMemory.carry (X := Saved B Δ k b n) prep)
      (Program.seq (initState B Δ k b n) (Program.seq (ProgramMemory.carry client) (finish B Δ k b n)))).runEncoded G
      (fun v => (input v, saved v)) = fun v => finishValue
        (client.run G (fun u => (((prep.runEncoded G input u).low, (saved u).2), prep.runEncoded G input u)) v, saved v) := by
  rw [Program.runEncoded_eq_run]
  change (finish B Δ k b n).run G ((ProgramMemory.carry client).run G
    ((initState B Δ k b n).run G ((ProgramMemory.carry prep).run G (fun v => (input v, saved v))))) = _
  rw [ProgramMemory.run G prep]
  change (finish B Δ k b n).run G ((ProgramMemory.carry client).run G
    (fun v => ((((prep.run G input v).low, (saved v).2), prep.run G input v), saved v))) = _
  rw [ProgramMemory.run G client]
  change (fun v => finishValue (client.run G (fun u => (((prep.run G input u).low, (saved u).2), prep.run G input u)) v, saved v)) = _
  simp only [Program.runEncoded_eq_run]

theorem run_program {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    (program I L Δ k t b n B).runEncoded G (fun v => (input v, (c v, β v))) = fun v => finishValue
      ((GeneralCoveringOwnerSimulation.translate I L Δ (ActiveFiniteBitPartition.program I Δ k t b n)).run G
        (fun u => (((GeneralCoveringOwnerSimulation.learned G I L Δ input u).low, β u),
          GeneralCoveringOwnerSimulation.learned G I L Δ input u)) v, (c v, β v)) :=
  prepared_run G (GeneralCoveringOwnerVirtualPrepare.program I L Δ)
    (GeneralCoveringOwnerSimulation.translate I L Δ (ActiveFiniteBitPartition.program I Δ k t b n)) input (fun v => (c v, β v))

theorem env_retained {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    ((program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v).env =
      GeneralCoveringOwnerSimulation.learned G I L Δ input v := by
  rw [run_program]
  exact GeneralCoveringOwnerSimulation.env_preserved G I L Δ (ActiveFiniteBitPartition.program I Δ k t b n) _ v

theorem coins_retained {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    ((program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v).coins = β v := by
  rw [run_program]
  rfl

theorem cost_retained {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    ((program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v).fields.cost = c v := by
  rw [run_program]
  rfl

theorem private_input_retained {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    ((program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v).env.metadata.owned.input = input v :=
  (congrArg (fun E : GeneralCoveringOwnerVirtualPrepare.Env V => E.metadata.owned.input)
    (env_retained G I L Δ k t b n B input c β v)).trans
    (GeneralCoveringOwnerVirtualPrepare.private_input_retained G I L Δ input v)

/-- Only interpretation of ORIGINAL private inputs; no learned metadata,
low mask, partition, neighbors, field, boundary or output inequality. -/
structure Original (input : V → GeneralCoveringOwners.Input V) where
  cover : V → Finset V
  targets : V → Finset V
  D : Finset V
  R : Finset V
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  center : ∀ v, (input v).center = decide (v ∈ D)
  demand : ∀ v, (input v).demand = decide (v ∈ R)
  candidates : ∀ v, (input v).candidates = cover v
  inverse : ∀ v, (input v).targets = targets v

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Entire native encoded execution, on the actual prepared public low graph. -/
theorem correct {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    (program I L Δ k t b n B).runEncoded G (fun v => (input v, (c v, β v))) = fun v => finishValue
      (((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded
          (GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L
            (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
          (fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image d.D
            (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)), β u)) v,
        GeneralCoveringOwnerSimulation.learned G I L Δ input v), (c v, β v)) := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G I d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hin : (fun u => ((GeneralCoveringOwnerSimulation.learned G I L Δ input u).low, β u)) =
      fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image d.D
        (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)), β u) := by
    funext u
    exact Prod.ext (hs.2.2.1 u) rfl
  rw [run_program, GeneralCoveringOwnerSimulation.translate_correct G I d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse (ActiveFiniteBitPartition.program I Δ k t b n),
    hin, Program.runEncoded_eq_run]

/-- Actual random SmallParts pullback. Coins remain on PUBLIC V; no law on
private Low identifiers or independent pulled-back slots is assumed. -/
noncomputable def partition {Δ k b n : ℕ} (cover : V → Finset V) (D R : Finset V) (L : ℕ)
    (hk : 0 < k) (t : ℕ) (β : V → Coins Δ k b n) :
    SmallParts.Data (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) Finset.univ k :=
  pulledPartition (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))
    (GeneralCoveringTaskPartitionMarks.lowEmbedding D _) Δ k hk t b n β

/-- Transport through graph equality without identifying dependent adjacency
instances definitionally. Deciders for a fixed relation are subsingletons. -/
private theorem run_graph_congr {In Out : Type} (P : Program V In Out)
    (H K : SimpleGraph V) (dH : DecidableRel H.Adj) (dK : DecidableRel K.Adj)
    (h : H = K) (s : V → In) :
    @Program.runEncoded V In Out _ _ H dH P s = @Program.runEncoded V In Out _ _ K dK P s := by
  cases h
  have hd : dH = dK := Subsingleton.elim _ _
  cases hd
  rfl

/-- Exact full physical output at a Low vertex of one actual random part. -/
theorem part_output {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n)
    (U : Finset (Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)))
    (hU : U ∈ (partition G d.cover d.D d.R L hk t β).parts)
    (i : Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) (hi : i ∈ U) :
    (program I L Δ k t b n B).runEncoded G (fun v => (input v, (c v, β v))) i.val.val =
      ⟨GeneralCoveringTaskRoles.fromLabel (c i.val.val) (U.image (GeneralCoveringTaskPartitionMarks.lowEmbedding d.D _))
          (decide (i ∉ BoundaryOwners.vertices (graph G d.cover d.D d.R L
            (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) Finset.univ
              (partition G d.cover d.D d.R L hk t β).parts)),
        U.image (GeneralCoveringTaskPartitionMarks.lowEmbedding d.D _),
        decide (i ∈ BoundaryOwners.vertices (graph G d.cover d.D d.R L
          (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) Finset.univ
            (partition G d.cover d.D d.R L hk t β).parts),
        GeneralCoveringOwnerSimulation.learned G I L Δ input i.val.val, β i.val.val⟩ := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let J := graph G d.cover d.D d.R L Q
  let e := GeneralCoveringTaskPartitionMarks.lowEmbedding d.D Q
  have hs := GeneralCoveringOwnerSimulation.learned_spec G I d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hm : i.val.val ∈ GeneralCoveringOwnerVirtualPrepare.image d.D Q :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hl : (GeneralCoveringOwnerSimulation.learned G I L Δ input i.val.val).low = true :=
    (hs.2.2.1 i.val.val).trans (decide_eq_true hm)
  have he := congrFun (correct G I L Δ k t b n B input d c β) i.val.val
  have hr := embedded_output J e I Δ k hk t ht b n β
    (GeneralCoveringTaskPhysicalMarks.low_degree G d.cover d.D d.R L Δ) U hU i hi
  have hgraph : GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L Q =
      PublicEmbedding.graph J e := GeneralCoveringTaskPhysicalMarks.publicGraph_eq G d.cover d.D d.R L Q
  have hactive : (fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image d.D Q), β u)) =
      fun u => (decide (u ∈ GeneralCoveringTaskPartitionMarks.activeImage e), β u) := by
    funext u
    exact congrArg (fun S : Finset V => (decide (u ∈ S), β u))
      (GeneralCoveringTaskPhysicalMarks.image_eq d.D Q)
  have hrun := run_graph_congr (ActiveFiniteBitPartition.program I Δ k t b n)
    (GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L Q) (PublicEmbedding.graph J e)
    (inferInstance) (fun _ _ => Classical.propDecidable _) hgraph
    (fun u => (decide (u ∈ GeneralCoveringTaskPartitionMarks.activeImage e), β u))
  have hraw : (ActiveFiniteBitPartition.program I Δ k t b n).runEncoded
      (GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L Q)
      (fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image d.D Q), β u)) i.val.val =
      (U.image e, decide (i ∈ BoundaryOwners.vertices J Finset.univ (pulledPartition J e Δ k hk t b n β).parts)) := by
    rw [hactive]
    exact (congrFun hrun i.val.val).trans hr
  rw [hraw] at he
  simpa [finishValue, hl] using he

theorem outside_low {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V)
    (hv : v ∉ GeneralCoveringOwnerVirtualPrepare.image d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) :
    (program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v =
      ⟨⟨c v, none, false⟩, ∅, false, GeneralCoveringOwnerSimulation.learned G I L Δ input v, β v⟩ := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G I d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hl : (GeneralCoveringOwnerSimulation.learned G I L Δ input v).low = false :=
    (hs.2.2.1 v).trans (decide_eq_false hv)
  have he := congrFun (correct G I L Δ k t b n B input d c β) v
  have hr := ActiveFiniteBitPartition.inactive
    (GeneralCoveringOwnerVirtualPrepare.publicGraph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
    I Δ k hk t ht b n (GeneralCoveringOwnerVirtualPrepare.image d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) β
    (GeneralCoveringOwnerVirtualPrepare.public_degree_bound G d.cover d.D d.R L Δ) v hv
  rw [hr] at he
  simpa [finishValue, hl, GeneralCoveringTaskRoles.fromLabel, MaskedMinimum.minimum] using he

theorem fields_spec {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
    let P := partition G d.cover d.D d.R L hk t β
    let out := (program I L Δ k t b n B).runEncoded G (fun v => (input v, (c v, β v)))
    (∀ v, (out v).fields.cost = c v) ∧
      (∀ (U : Finset (Low d.D Q)) (hU : U ∈ P.parts) (i : Low d.D Q), i ∈ U →
        (out i.val.val).label = U.image (GeneralCoveringTaskPartitionMarks.lowEmbedding d.D Q) ∧
        (out i.val.val).fields.role = some (GeneralCoveringTaskRoles.name d.D Q U (P.nonempty U hU))) ∧
      (∀ z : d.D, z ∈ Q → (out z.val).fields.role = none) ∧
      (∀ i : Low d.D Q, (out i.val.val).fields.interior =
        decide (i ∉ BoundaryOwners.vertices (graph G d.cover d.D d.R L Q) Finset.univ P.parts)) ∧
      (∀ v, (out v).env = GeneralCoveringOwnerSimulation.learned G I L Δ input v) ∧
      (∀ v, (out v).coins = β v) ∧ (∀ v, (out v).env.metadata.owned.input = input v) := by
  dsimp only
  refine ⟨cost_retained G I L Δ k t b n B input c β, ?_, ?_, ?_,
    env_retained G I L Δ k t b n B input c β, coins_retained G I L Δ k t b n B input c β,
    private_input_retained G I L Δ k t b n B input c β⟩
  · intro U hU i hi
    rw [part_output G I L Δ k hk t ht b n B input d c β U hU i hi]
    exact ⟨rfl, GeneralCoveringTaskRoles.name_option d.D _ U ((partition G d.cover d.D d.R L hk t β).nonempty U hU)⟩
  · intro z hz
    have hn : z.val ∉ GeneralCoveringOwnerVirtualPrepare.image d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) := by
      rintro hv
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hv
      have hez : i.val = z := Subtype.ext he
      exact i.property (hez.symm ▸ hz)
    rw [outside_low G I L Δ k hk t ht b n B input d c β z.val hn]
  · intro i
    obtain ⟨U, hU, hi⟩ := (partition G d.cover d.D d.R L hk t β).covers i (Finset.mem_univ i)
    rw [part_output G I L Δ k hk t ht b n B input d c β U hU i hi]
    rfl

theorem empty_centers {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    (hD : d.D = ∅) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    (program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v =
      ⟨⟨c v, none, false⟩, ∅, false, GeneralCoveringOwnerSimulation.learned G I L Δ input v, β v⟩ := by
  apply outside_low G I L Δ k hk t ht b n B input d c β v
  intro hv
  obtain ⟨i, _, _⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image d.D _ v).mp hv
  exact Finset.notMem_empty _ ((congrArg (fun S : Finset V => (i.val : V) ∈ S) hD).mp i.property)

theorem empty_low {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V) (d : Original G input)
    [IsEmpty (Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))]
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) (v : V) :
    (program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v =
      ⟨⟨c v, none, false⟩, ∅, false, GeneralCoveringOwnerSimulation.learned G I L Δ input v, β v⟩ := by
  apply outside_low G I L Δ k hk t ht b n B input d c β v
  rintro hv
  obtain ⟨i, _, _⟩ := Finset.mem_image.mp hv
  exact isEmptyElim i

theorem empty_physical [IsEmpty V] {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    (program I L Δ k t b n B).runEncoded G (fun v => (input v, (c v, β v))) =
      fun v => ⟨⟨c v, none, false⟩, ∅, false, GeneralCoveringOwnerSimulation.learned G I L Δ input v, β v⟩ := by
  funext v
  exact isEmptyElim v
end Physical

theorem bits_per_vertex (Δ k b n : ℕ) :
    Fintype.card (CurrentFiniteBitPartition.Index Δ k n × Fin b) = n * 2 ^ ((Δ + 1) ^ k) * b :=
  ActiveFiniteBitPartition.bits_per_vertex Δ k b n

theorem rounds {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ) :
    (program I L Δ k t b n B).rounds = 10 + 4 * (n * (3 * k + 1) + 1) := by
  simp only [program, initState, finish, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringOwnerVirtualPrepare.rounds, GeneralCoveringOwnerSimulation.rounds,
    ActiveFiniteBitPartition.rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ) :
    (program I L Δ k t b n B).maxBits ≤
      (L + Δ + 3) * (ids + (ActiveFiniteBitPartition.program I Δ k t b n).maxBits + 2) := by
  simp only [program, initState, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le
  · exact (GeneralCoveringOwnerVirtualPrepare.maxBits I L Δ).trans (by nlinarith)
  · exact (GeneralCoveringOwnerSimulation.maxBits I L Δ (ActiveFiniteBitPartition.program I Δ k t b n)).trans (by nlinarith)

theorem packet_bound {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ) :
    (program I L Δ k t b n B).maxBits ≤ (L + Δ + 3) *
      (ids + max (ActiveFiniteBitPartition.packetBound ids Δ k b n) (k * (ids + 1)) + 2) := by
  apply (maxBits I L Δ k t b n B).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left
    (ActiveFiniteBitPartition.maxBits I Δ k t b n) ids) 2)

def bitCoefficient (L Δ k b n c : ℕ) : ℕ :=
  (L + Δ + 3) * (c + ActiveFiniteBitPartition.bitCoefficient Δ k b n c + 2)

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B c : ℕ)
    (hids : ids ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program I L Δ k t b n B).maxBits ≤ bitCoefficient L Δ k b n c * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := ActiveFiniteBitPartition.logarithmic_bits I Δ k t b n (Fintype.card V) c hids
  have hl : 1 ≤ Nat.clog 2 (Fintype.card V + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : ids + (ActiveFiniteBitPartition.program I Δ k t b n).maxBits + 2 ≤
      (c + ActiveFiniteBitPartition.bitCoefficient Δ k b n c + 2) * Nat.clog 2 (Fintype.card V + 2) := by
    nlinarith
  apply (maxBits I L Δ k t b n B).trans
  simpa only [bitCoefficient, Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

end Paper.GeneralCoveringTaskRandomPhysicalMarks

#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.label_image
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.embedded_output
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.run_program
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.env_retained
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.coins_retained
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.cost_retained
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.private_input_retained
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.correct
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.part_output
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.outside_low
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.fields_spec
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.empty_centers
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.empty_low
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.empty_physical
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.bits_per_vertex
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.rounds
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.maxBits
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.packet_bound
#print axioms Paper.GeneralCoveringTaskRandomPhysicalMarks.logarithmic_bits
