import Paper.Solver.LocalSearch.GeneralCoveringOwnerVirtualPrepare

/-! Literal arbitrary-program compiler for actual optional C-owners.
Every broadcast uses the accepted four-round payload CORE. The learned Env
is private immutable state. execute computes it once from original private
incidence input, then runs the structural local/broadcast/seq translation.
The only fallback is the sender's own already computed message; correctness
proves Some(correct message) for every queried virtual neighbor. -/
namespace Paper.GeneralCoveringOwnerSimulation
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

def prepare {In Out Msg : Type} (R0 : Round V In Out Msg) :
    Program V (In × GeneralCoveringOwnerVirtualPrepare.Env V)
      (GeneralCoveringOwnerPayloadRoute.Input V Msg × ((In × GeneralCoveringOwnerVirtualPrepare.Env V) × Msg)) :=
  .local fun v _ s =>
    let msg := R0.send v s.2.neighbors s.1
    (⟨s.2.metadata, s.2.low, msg⟩, (s, msg))

def finish {In Out Msg : Type} (R0 : Round V In Out Msg) :
    Program V (GeneralCoveringOwnerPayloadRoute.Output V Msg × ((In × GeneralCoveringOwnerVirtualPrepare.Env V) × Msg))
      (Out × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .local fun v _ s =>
    let saved := s.2.1
    (R0.update v saved.2.neighbors saved.1
      (fun u => (TaggedDictionary.lookup s.1.payloads u.val).getD s.2.2), saved.2)

def simulateRound {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (L Δ : ℕ) (R0 : Round V In Out Msg) :
    Program V (In × GeneralCoveringOwnerVirtualPrepare.Env V) (Out × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .seq (prepare R0) (.seq (ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.route ids code L Δ)) (finish R0))

/-- Literal graph-independent structural translation. -/
def translate {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} :
    Program V In Out → Program V (In × GeneralCoveringOwnerVirtualPrepare.Env V) (Out × GeneralCoveringOwnerVirtualPrepare.Env V)
  | .local f => .local fun v _ s => (f v s.2.neighbors s.1, s.2)
  | .broadcast _ code R0 => simulateRound ids code L Δ R0
  | .seq P Q => .seq (translate ids L Δ P) (translate ids L Δ Q)

/-- The actual ten-round preparer runs exactly once, before translation. -/
def execute {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    Program V (GeneralCoveringOwners.Input V × In) (Out × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .seq (ProgramMemory.carry (GeneralCoveringOwnerVirtualPrepare.program ids L Δ))
    (.seq (.local fun _ _ s => (s.2, s.1)) (translate ids L Δ P))

theorem round_rounds {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (L Δ : ℕ) (R0 : Round V In Out Msg) : (simulateRound ids code L Δ R0).rounds = 4 := rfl

theorem rounds {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate ids L Δ P).rounds = 4 * P.rounds := by
  induction P with
  | «local» f => rfl
  | broadcast w code R0 => rfl
  | seq P Q ihP ihQ => simp only [translate, Program.rounds, ihP, ihQ, Nat.mul_add]

theorem round_maxBits {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (L Δ : ℕ) (R0 : Round V In Out Msg) :
    (simulateRound ids code L Δ R0).maxBits ≤ (L + Δ + 3) * (b + w + 1) := by
  simp only [simulateRound, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact GeneralCoveringOwnerPayloadRoute.route_maxBits ids code L Δ

theorem maxBits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (translate ids L Δ P).maxBits ≤ (L + Δ + 3) * (b + P.maxBits + 1) := by
  induction P with
  | «local» f => exact Nat.zero_le _
  | broadcast w code R0 => exact round_maxBits ids code L Δ R0
  | seq P Q ihP ihQ =>
    apply max_le
    · exact ihP.trans (Nat.mul_le_mul_left _ (by change b + P.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))
    · exact ihQ.trans (Nat.mul_le_mul_left _ (by change b + Q.maxBits + 1 ≤ b + max P.maxBits Q.maxBits + 1; omega))

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (n c d : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (translate ids L Δ P).maxBits ≤ ((L + Δ + 3) * (c + d + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + P.maxBits + 1 ≤ (c + d + 1) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits ids L Δ P).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

theorem execute_rounds {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute ids L Δ P).rounds = 10 + 4 * P.rounds := by
  simp only [execute, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerVirtualPrepare.rounds,
    rounds, Nat.zero_add]

theorem execute_maxBits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    (execute ids L Δ P).maxBits ≤ (L + Δ + 3) * (b + P.maxBits + 2) := by
  simp only [execute, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]
  apply max_le
  · exact (GeneralCoveringOwnerVirtualPrepare.maxBits ids L Δ).trans (by nlinarith)
  · exact (maxBits ids L Δ P).trans (by nlinarith)

theorem execute_logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (n c d : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (execute ids L Δ P).maxBits ≤ ((L + Δ + 3) * (c + d + 2)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + P.maxBits + 2 ≤ (c + d + 2) * Nat.clog 2 (n + 2) := by nlinarith
  apply (execute_maxBits ids L Δ P).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem round_run {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (L Δ : ℕ) (R0 : Round V In Out Msg) (s : V → In × GeneralCoveringOwnerVirtualPrepare.Env V) :
    (simulateRound ids code L Δ R0).run G s =
      let msg := fun v => R0.send v (s v).2.neighbors (s v).1
      let inputs := fun v => (⟨(s v).2.metadata, (s v).2.low, msg v⟩ : GeneralCoveringOwnerPayloadRoute.Input V Msg)
      let data := (GeneralCoveringOwnerPayloadRoute.route ids code L Δ).run G inputs
      fun v => (R0.update v (s v).2.neighbors (s v).1
        (fun u => (TaggedDictionary.lookup (data v).payloads u.val).getD (msg v)), (s v).2) := by
  change (finish R0).run G ((ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.route ids code L Δ)).run G
    (fun v => ((⟨(s v).2.metadata, (s v).2.low, R0.send v (s v).2.neighbors (s v).1⟩ : GeneralCoveringOwnerPayloadRoute.Input V Msg),
      (s v, R0.send v (s v).2.neighbors (s v).1)))) = _
  rw [ProgramMemory.run G (GeneralCoveringOwnerPayloadRoute.route ids code L Δ)]
  rfl

theorem round_env {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (L Δ : ℕ) (R0 : Round V In Out Msg) (s : V → In × GeneralCoveringOwnerVirtualPrepare.Env V) (v : V) :
    ((simulateRound ids code L Δ R0).run G s v).2 = (s v).2 := by
  rw [round_run]

theorem env_preserved {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out) :
    ∀ s : V → In × GeneralCoveringOwnerVirtualPrepare.Env V, ∀ v,
      ((translate ids L Δ P).run G s v).2 = (s v).2 := by
  induction P with
  | «local» f => intro s v; rfl
  | broadcast w code R0 => intro s v; exact round_env G ids code L Δ R0 s v
  | seq P Q ihP ihQ =>
    intro s v
    exact (ihQ ((translate ids L Δ P).run G s) v).trans (ihP s v)

def learned {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :=
  (GeneralCoveringOwnerVirtualPrepare.program ids L Δ).runEncoded G input

theorem learned_eq_run {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    learned G ids L Δ input = (GeneralCoveringOwnerVirtualPrepare.program ids L Δ).run G input :=
  Program.runEncoded_eq_run G _ input

theorem execute_run {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (input : V → GeneralCoveringOwners.Input V) (s : V → In) :
    (execute ids L Δ P).run G (fun v => (input v, s v)) =
      (translate ids L Δ P).run G (fun v => (s v, (GeneralCoveringOwnerVirtualPrepare.program ids L Δ).run G input v)) := by
  change (translate ids L Δ P).run G ((Program.local fun _ _ z => (z.2, z.1)).run G
    ((ProgramMemory.carry (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)).run G (fun v => (input v, s v)))) = _
  rw [ProgramMemory.run G (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)]
  rfl

theorem execute_env {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (input : V → GeneralCoveringOwners.Input V) (s : V → In) (v : V) :
    ((execute ids L Δ P).runEncoded G (fun u => (input u, s u)) v).2 = learned G ids L Δ input v := by
  rw [Program.runEncoded_eq_run, execute_run, learned_eq_run]
  exact env_preserved G ids L Δ P _ v

theorem execute_private_input_retained {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) {In Out : Type} (P : Program V In Out)
    (input : V → GeneralCoveringOwners.Input V) (s : V → In) (v : V) :
    ((execute ids L Δ P).runEncoded G (fun u => (input u, s u)) v).2.metadata.owned.input = input v := by
  calc
    _ = (learned G ids L Δ input v).metadata.owned.input :=
      congrArg (fun e : GeneralCoveringOwnerVirtualPrepare.Env V => e.metadata.owned.input)
        (execute_env G ids L Δ P input s v)
    _ = input v := GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringTaskGeometry.graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- These facts are derived from actual private preparation, never supplied to code. -/
theorem learned_spec {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    (∀ v, (learned G ids L Δ input v).metadata = GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v) ∧
    (∀ v, (learned G ids L Δ input v).metadata.owned.input = input v) ∧
    (∀ v, (learned G ids L Δ input v).low = decide (v ∈ GeneralCoveringOwnerVirtualPrepare.image D
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ))) ∧
    (∀ v, (learned G ids L Δ input v).neighbors = (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) := by
  have h := GeneralCoveringOwnerVirtualPrepare.private_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  exact ⟨fun v => (h.1 v).1, fun v => (h.1 v).2.1, h.2.2.1, h.2.2.2.1⟩

theorem neighbor_lifts (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (v u : V)
    (hu : u ∈ (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) :
    ∃ i j : Low D (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ),
      (GeneralCoveringTaskGeometry.graph G C D R L (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj i j ∧
      i.val.val = v ∧ j.val.val = u := by
  exact (PublicEmbedding.adj_iff
    (GeneralCoveringTaskGeometry.graph G C D R L (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ))
    (GeneralCoveringOwnerVirtualPrepare.embedding D _) v u).mp
      (((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).mem_neighborFinset v u).mp hu)

/-- Some(correct payload) for EVERY queried low-graph neighbor, derived from
actual learned metadata and the accepted router, not a delivery assumption. -/
theorem routed_neighbor {A : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode A w)
    (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) (f : V → A) (v u : V)
    (hu : u ∈ (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) :
    TaggedDictionary.lookup ((GeneralCoveringOwnerPayloadRoute.route ids code L Δ).run G
      (fun z => ⟨(learned G ids L Δ input z).metadata, (learned G ids L Δ input z).low, f z⟩) v).payloads u = some (f u) := by
  have hs := learned_spec G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  let t : V → GeneralCoveringOwnerPayloadRoute.PrivateInput V A :=
    fun z => ⟨input z, (learned G ids L Δ input z).low, f z⟩
  have he : (fun z => (⟨(learned G ids L Δ input z).metadata, (learned G ids L Δ input z).low, f z⟩ :
      GeneralCoveringOwnerPayloadRoute.Input V A)) = GeneralCoveringOwnerPayloadRoute.expected G C D R L t := by
    funext z
    change GeneralCoveringOwnerPayloadRoute.Input.mk (learned G ids L Δ input z).metadata
      (learned G ids L Δ input z).low (f z) =
      ⟨GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input z, (learned G ids L Δ input z).low, f z⟩
    rw [hs.1 z]
  rw [he]
  obtain ⟨i, j, hij, hi, hj⟩ := neighbor_lifts G C D R L Δ v u hu
  subst v
  subst u
  apply GeneralCoveringOwnerPayloadRoute.lookup_correct G ids code C D R L Δ hlocal t hD i.val
    (GeneralCoveringOwnerVirtualPrepare.low_degree G C D R L Δ i) j.val.val
  · exact Finset.mem_image.mpr ⟨j.val, ((ownerGraph G C D R L).mem_neighborFinset i.val j.val).mpr hij, rfl⟩
  · have hjimage : j.val.val ∈ GeneralCoveringOwnerVirtualPrepare.image D
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ) :=
      (GeneralCoveringOwnerVirtualPrepare.mem_image D _ j.val.val).mpr ⟨j.val, rfl, j.property⟩
    exact (hs.2.2.1 j.val.val).trans (decide_eq_true hjimage)

/-- The actual round's physical route answers every learned-neighbor query;
the saved own-message fallback in finish is therefore never used. -/
theorem round_lookup {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) (R0 : Round V In Out Msg) (s : V → In) (v u : V)
    (hu : u ∈ (learned G ids L Δ input v).neighbors) :
    TaggedDictionary.lookup ((GeneralCoveringOwnerPayloadRoute.route ids code L Δ).run G
      (fun z => ⟨(learned G ids L Δ input z).metadata, (learned G ids L Δ input z).low,
        R0.send z (learned G ids L Δ input z).neighbors (s z)⟩) v).payloads u =
      some (R0.send u (learned G ids L Δ input u).neighbors (s u)) := by
  have hn := (learned_spec G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets).2.2.2 v
  have hu' : u ∈ (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v := by
    rw [← hn]
    exact hu
  exact routed_neighbor G ids code C targets D R L Δ hinc hlocal input hD hR hC hTargets
    (fun z => R0.send z (learned G ids L Δ input z).neighbors (s z)) v u hu'

theorem round_correct {In Out Msg : Type} {b w : ℕ} (ids : BitCode V b) (code : BitCode Msg w)
    (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) (R0 : Round V In Out Msg) (s : V → In) :
    (simulateRound ids code L Δ R0).run G (fun v => (s v, learned G ids L Δ input v)) = fun v =>
      (eval (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) R0 s v, learned G ids L Δ input v) := by
  have hs := learned_spec G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  let f := fun v => R0.send v ((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
    (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) (s v)
  have hin : (fun v => (⟨(learned G ids L Δ input v).metadata, (learned G ids L Δ input v).low,
      R0.send v (learned G ids L Δ input v).neighbors (s v)⟩ : GeneralCoveringOwnerPayloadRoute.Input V Msg)) =
      fun v => ⟨(learned G ids L Δ input v).metadata, (learned G ids L Δ input v).low, f v⟩ := by
    funext v
    rw [hs.2.2.2 v]
  rw [round_run]
  dsimp only
  rw [hin]
  funext v
  refine Prod.ext ?_ rfl
  change R0.update v (learned G ids L Δ input v).neighbors (s v) (fun u =>
    (TaggedDictionary.lookup ((GeneralCoveringOwnerPayloadRoute.route ids code L Δ).run G
      (fun z => ⟨(learned G ids L Δ input z).metadata, (learned G ids L Δ input z).low, f z⟩) v).payloads u.val).getD
        (R0.send v (learned G ids L Δ input v).neighbors (s v))) =
    R0.update v ((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) (s v)
      (fun u => R0.send u.val ((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset u.val) (s u.val))
  rw [hs.2.2.2 v]
  apply congrArg (R0.update v ((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
    (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) (s v))
  funext u
  have hu := routed_neighbor G ids code C targets D R L Δ hinc hlocal input hD hR hC hTargets f v u.val u.property
  simpa only [Option.getD_some] using congrArg (fun q : Option Msg => q.getD
    (R0.send v ((GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset v) (s v))) hu

/-- Structural induction for the WHOLE client Program, including isolated
physical IDs outside the low-owner image. -/
theorem translate_correct {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) {In Out : Type} (P : Program V In Out) : ∀ s : V → In,
    (translate ids L Δ P).run G (fun v => (s v, learned G ids L Δ input v)) = fun v =>
      (P.run (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) s v, learned G ids L Δ input v) := by
  induction P with
  | «local» f =>
    intro s
    funext v
    exact Prod.ext (congrArg (fun N : Finset V => f v N (s v))
      ((learned_spec G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets).2.2.2 v)) rfl
  | broadcast w code R0 =>
    intro s
    exact round_correct G ids code C targets D R L Δ hinc hlocal input hD hR hC hTargets R0 s
  | seq P Q ihP ihQ =>
    intro s
    change (translate ids L Δ Q).run G
      ((translate ids L Δ P).run G (fun v => (s v, learned G ids L Δ input v))) = _
    rw [ihP s]
    exact ihQ _

/-- Native encoded execute: preparation from private original C/incidence
input ONCE, then arbitrary client program on the exact public low graph. -/
theorem execute_correct {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) {In Out : Type} (P : Program V In Out) (s : V → In) :
    (execute ids L Δ P).runEncoded G (fun v => (input v, s v)) = fun v =>
      (P.run (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) s v, learned G ids L Δ input v) := by
  rw [Program.runEncoded_eq_run, execute_run, ← learned_eq_run G ids L Δ input]
  exact translate_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets P s

end Paper.GeneralCoveringOwnerSimulation

#print axioms Paper.GeneralCoveringOwnerSimulation.round_rounds
#print axioms Paper.GeneralCoveringOwnerSimulation.rounds
#print axioms Paper.GeneralCoveringOwnerSimulation.round_maxBits
#print axioms Paper.GeneralCoveringOwnerSimulation.maxBits
#print axioms Paper.GeneralCoveringOwnerSimulation.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_rounds
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_maxBits
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerSimulation.round_run
#print axioms Paper.GeneralCoveringOwnerSimulation.round_env
#print axioms Paper.GeneralCoveringOwnerSimulation.env_preserved
#print axioms Paper.GeneralCoveringOwnerSimulation.learned_eq_run
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_run
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_env
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_private_input_retained
#print axioms Paper.GeneralCoveringOwnerSimulation.learned_spec
#print axioms Paper.GeneralCoveringOwnerSimulation.neighbor_lifts
#print axioms Paper.GeneralCoveringOwnerSimulation.routed_neighbor
#print axioms Paper.GeneralCoveringOwnerSimulation.round_lookup
#print axioms Paper.GeneralCoveringOwnerSimulation.round_correct
#print axioms Paper.GeneralCoveringOwnerSimulation.translate_correct
#print axioms Paper.GeneralCoveringOwnerSimulation.execute_correct
