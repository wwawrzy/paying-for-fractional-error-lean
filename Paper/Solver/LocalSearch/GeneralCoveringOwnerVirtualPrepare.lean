import Paper.Solver.LocalSearch.GeneralCoveringOwnerPayloadRoute
import Paper.Preliminaries.PublicEmbedding

/-! Ten-round actual-C preparation of the public low-owner graph. The
six-round Discovery producer runs once; its private metadata, capped list
and high bit are carried through the four-round CORE payload router.
Every center sends its actual high bit. Only low centers retain neighbors
whose received bit is false. Public embeddings below are analysis only. -/
namespace Paper.GeneralCoveringOwnerVirtualPrepare
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

structure Env (V : Type) where
  metadata : GeneralCoveringOwnerSupport.State V
  discovered : Finset V
  high : Bool
  low : Bool
  neighbors : Finset V

def assemble (d : GeneralCoveringOwnerDiscovery.Output V) (xs : List (V × Bool)) : Env V :=
  let low := d.metadata.owned.input.center && !d.high
  ⟨d.metadata, d.neighbors, d.high, low,
    if low then d.neighbors.filter (fun j => TaggedDictionary.lookup xs j = some false) else ∅⟩

def routeInput (d : GeneralCoveringOwnerDiscovery.Output V) : GeneralCoveringOwnerPayloadRoute.Input V Bool :=
  ⟨d.metadata, d.metadata.owned.input.center, d.high⟩

def prepareRoute : Program V (GeneralCoveringOwnerDiscovery.Output V)
    (GeneralCoveringOwnerPayloadRoute.Input V Bool × GeneralCoveringOwnerDiscovery.Output V) :=
  .local fun _ _ s => (routeInput s, s)

def finish : Program V (GeneralCoveringOwnerPayloadRoute.Output V Bool × GeneralCoveringOwnerDiscovery.Output V) (Env V) :=
  .local fun _ _ s => assemble s.2 s.1.payloads

/-- Public ids,L,Delta only. Discovery computes all private support metadata once. -/
def program {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Env V) :=
  .seq (GeneralCoveringOwnerDiscovery.program ids L Δ) (.seq prepareRoute
    (.seq (ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.route ids BitCode.bool L Δ)) finish))

theorem assemble_empty (d : GeneralCoveringOwnerDiscovery.Output V) (xs : List (V × Bool))
    (hl : (assemble d xs).low = false) : (assemble d xs).neighbors = ∅ := by
  change (d.metadata.owned.input.center && !d.high) = false at hl
  change (if d.metadata.owned.input.center && !d.high then _ else ∅) = ∅
  simp only [hl, Bool.false_eq_true, ↓reduceIte]

theorem rounds {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) : (program ids L Δ).rounds = 10 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) :
    (program ids L Δ).maxBits ≤ (L + Δ + 3) * (b + 2) := by
  simp only [program, prepareRoute, finish, Program.maxBits, ProgramMemory.maxBits,
    Nat.zero_max, Nat.max_zero]
  apply max_le
  · exact (GeneralCoveringOwnerDiscovery.maxBits ids L Δ).trans (by nlinarith)
  · simpa only [Nat.add_assoc] using
      GeneralCoveringOwnerPayloadRoute.route_maxBits ids BitCode.bool L Δ

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program ids L Δ).maxBits ≤ ((L + Δ + 3) * (c + 2)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + 2 ≤ (c + 2) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits ids L Δ).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def discovery {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :=
  (GeneralCoveringOwnerDiscovery.program ids L Δ).run G input

def dictionary {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) (v : V) : List (V × Bool) :=
  ((GeneralCoveringOwnerPayloadRoute.route ids BitCode.bool L Δ).run G
    (fun u => routeInput (discovery G ids L Δ input u)) v).payloads

theorem run_program {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ).run G input = fun v =>
      assemble (discovery G ids L Δ input v) (dictionary G ids L Δ input v) := by
  change finish.run G ((ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.route ids BitCode.bool L Δ)).run G
    (fun u => (routeInput (discovery G ids L Δ input u), discovery G ids L Δ input u))) = _
  rw [ProgramMemory.run G (GeneralCoveringOwnerPayloadRoute.route ids BitCode.bool L Δ)]
  rfl

theorem encoded_run {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ).runEncoded G input = fun v =>
      assemble (discovery G ids L Δ input v) (dictionary G ids L Δ input v) :=
  (Program.runEncoded_eq_run G _ input).trans (run_program G ids L Δ input)

theorem metadata_retained {b : ℕ} (ids : BitCode V b) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ).runEncoded G input v).metadata = (discovery G ids L Δ input v).metadata := by
  rw [encoded_run]
  rfl

theorem private_input_retained {b : ℕ} (ids : BitCode V b) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ).runEncoded G input v).metadata.owned.input = input v := by
  rw [metadata_retained]
  exact GeneralCoveringOwnerDiscovery.private_input_retained G ids L Δ input v

/-- Inject the actual induced low-owner graph into physical IDs. No subtype
inverse or globally known vertex set is supplied to any runtime program. -/
def embedding (D : Finset V) (Q : Finset D) : Low D Q ↪ V :=
  ⟨fun i => i.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

noncomputable def image (D : Finset V) (Q : Finset D) : Finset V := Finset.univ.image (embedding D Q)

theorem mem_image (D : Finset V) (Q : Finset D) (v : V) :
    v ∈ image D Q ↔ ∃ i : D, i.val = v ∧ i ∉ Q := by
  simp only [image, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i.val, he, i.property⟩
  · rintro ⟨i, he, hi⟩
    exact ⟨⟨i, hi⟩, he⟩

theorem range_eq (D : Finset V) (Q : Finset D) : Set.range (embedding D Q) = (image D Q : Set V) := by
  ext v
  simp only [Set.mem_range, Finset.mem_coe, image, Finset.mem_image, Finset.mem_univ, true_and]

theorem low_image (D : Finset V) (Q : Finset D) (v : V) (hv : v ∈ D) :
    v ∈ image D Q ↔ (⟨v, hv⟩ : D) ∉ Q := by
  rw [mem_image]
  constructor
  · rintro ⟨i, he, hi⟩
    have heq : i = (⟨v, hv⟩ : D) := Subtype.ext he
    rwa [heq] at hi
  · intro hi
    exact ⟨⟨v, hv⟩, rfl, hi⟩

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringTaskGeometry.graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def high (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) : Finset D :=
  Finset.univ.filter (fun i => Δ < (ownerGraph G C D R L).degree i)

theorem mem_high (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (i : D) :
    i ∈ high G C D R L Δ ↔ Δ < (ownerGraph G C D R L).degree i := by simp [high]

theorem low_degree (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (i : Low D (high G C D R L Δ)) : (ownerGraph G C D R L).degree i.val ≤ Δ := by
  have hn : ¬ Δ < (ownerGraph G C D R L).degree i.val :=
    fun hh => i.property ((mem_high G C D R L Δ i.val).mpr hh)
  omega

noncomputable def publicGraph (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) : SimpleGraph V :=
  PublicEmbedding.graph (GeneralCoveringTaskGeometry.graph G C D R L Q) (embedding D Q)

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (publicGraph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem neighbor_filter (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) (i : Low D Q) :
    (publicGraph G C D R L Q).neighborFinset i.val.val =
      (((ownerGraph G C D R L).neighborFinset i.val).filter (fun j => j ∉ Q)).image Subtype.val := by
  ext v
  rw [SimpleGraph.mem_neighborFinset]
  change (PublicEmbedding.graph (GeneralCoveringTaskGeometry.graph G C D R L Q)
    (embedding D Q)).Adj ((embedding D Q) i) v ↔ _
  rw [PublicEmbedding.adj_iff]
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, j, haj, ha, hj⟩
    have he : a = i := (embedding D Q).injective ha
    subst a
    exact ⟨j.val, ⟨((ownerGraph G C D R L).mem_neighborFinset i.val j.val).mpr haj, j.property⟩, hj⟩
  · rintro ⟨j, ⟨hj, hlow⟩, he⟩
    exact ⟨i, ⟨j, hlow⟩, ((ownerGraph G C D R L).mem_neighborFinset i.val j).mp hj, rfl, he⟩

theorem neighbor_outside (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (v : V) (hv : v ∉ image D Q) : (publicGraph G C D R L Q).neighborFinset v = ∅ := by
  apply PublicEmbedding.neighbor_outside _ (embedding D Q) v
  rwa [range_eq]

/-- The concrete graph supplied to later simulation has actual maximum degree Delta. -/
theorem public_degree_bound (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    ∀ v, (publicGraph G C D R L (high G C D R L Δ)).degree v ≤ Δ := by
  apply PublicEmbedding.degree_bound _ (embedding D _) Δ
  intro i
  have hc := Finset.card_le_card_of_injOn (fun j : Low D (high G C D R L Δ) => j.val)
    (s := (GeneralCoveringTaskGeometry.graph G C D R L (high G C D R L Δ)).neighborFinset i)
    (t := (ownerGraph G C D R L).neighborFinset i.val)
    (fun j hj => ((ownerGraph G C D R L).mem_neighborFinset _ _).mpr
      (((GeneralCoveringTaskGeometry.graph G C D R L (high G C D R L Δ)).mem_neighborFinset _ _).mp hj))
    (fun _ _ _ _ h => Subtype.ext h)
  change (GeneralCoveringTaskGeometry.graph G C D R L (high G C D R L Δ)).degree i ≤
    (ownerGraph G C D R L).degree i.val at hc
  exact hc.trans (low_degree G C D R L Δ i)

/-- Exact environment from the literal encoded ten-round producer. All
incidence data is private, and the only locality premise concerns original R.
The dictionary clause witnesses the actual delivery of computed high flags. -/
theorem private_correct {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V)
    (D R : Finset V) (L Δ : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (input : V → GeneralCoveringOwners.Input V)
    (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v) :
    let out := (program ids L Δ).runEncoded G input
    (∀ v, (out v).metadata = GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v ∧
      (out v).metadata.owned.input = input v ∧
      (out v).discovered = (discovery G ids L Δ input v).neighbors) ∧
    (∀ i : D, (out i.val).high = decide (Δ < (ownerGraph G C D R L).degree i)) ∧
    (∀ v, (out v).low = decide (v ∈ image D (high G C D R L Δ))) ∧
    (∀ v, (out v).neighbors = (publicGraph G C D R L (high G C D R L Δ)).neighborFinset v) ∧
    (∀ i j : D, (ownerGraph G C D R L).degree i ≤ Δ → (ownerGraph G C D R L).Adj i j →
      TaggedDictionary.lookup (dictionary G ids L Δ input i.val) j.val =
        some (decide (Δ < (ownerGraph G C D R L).degree j))) ∧
    (∀ v ∉ D, (out v).high = false) ∧
    (∀ v, GeneralCoveringOwners.owner C D R v = none ∨ v ∉ D ∨ (out v).high = true →
      (out v).neighbors = ∅) := by
  let d := discovery G ids L Δ input
  let Q := high G C D R L Δ
  have hd := GeneralCoveringOwnerDiscoveryCorrect.private_correct G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets
  rw [Program.runEncoded_eq_run] at hd
  obtain ⟨hm, hi, hcent, houtside, _⟩ := hd
  change (∀ v, (d v).metadata = GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v) at hm
  change (∀ v, (d v).metadata.owned.input = input v) at hi
  change (∀ i : D, (d i.val).neighbors = GeneralCoveringOwnerDiscoveryCorrect.capped G C D R L Δ i.val ∧
    (d i.val).high = decide (Δ < (ownerGraph G C D R L).degree i) ∧
    (d i.val).neighbors ⊆ GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i ∧
    ((ownerGraph G C D R L).degree i ≤ Δ →
      (d i.val).neighbors = GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i)) at hcent
  change (∀ v, v ∉ D → d v = ⟨GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v, ∅, false⟩) at houtside
  let t : V → GeneralCoveringOwnerPayloadRoute.PrivateInput V Bool :=
    fun v => ⟨input v, (input v).center, (d v).high⟩
  have ht : (fun v => routeInput (d v)) = GeneralCoveringOwnerPayloadRoute.expected G C D R L t := by
    funext v
    change GeneralCoveringOwnerPayloadRoute.Input.mk (d v).metadata
      (d v).metadata.owned.input.center (d v).high =
      ⟨GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v, (input v).center, (d v).high⟩
    rw [hi v, hm v]
  have hlook (i j : D) (hl : (ownerGraph G C D R L).degree i ≤ Δ)
      (ha : (ownerGraph G C D R L).Adj i j) :
      TaggedDictionary.lookup (dictionary G ids L Δ input i.val) j.val = some (d j.val).high := by
    change TaggedDictionary.lookup ((GeneralCoveringOwnerPayloadRoute.route ids BitCode.bool L Δ).run G
      (fun v => routeInput (d v)) i.val).payloads j.val = _
    rw [ht]
    exact GeneralCoveringOwnerPayloadRoute.lookup_correct G ids BitCode.bool C D R L Δ hlocal t hD i hl j.val
      (Finset.mem_image.mpr ⟨j, ((ownerGraph G C D R L).mem_neighborFinset i j).mpr ha, rfl⟩)
      ((hD j.val).trans (decide_eq_true j.property))
  have hmark (i : D) : (d i.val).high = decide (i ∈ Q) :=
    ((hcent i).2.1).trans (Bool.decide_congr (mem_high G C D R L Δ i).symm)
  have hl (v : V) : (assemble (d v) (dictionary G ids L Δ input v)).low = decide (v ∈ image D Q) := by
    change ((d v).metadata.owned.input.center && !(d v).high) = _
    rw [hi v, hD v]
    by_cases hv : v ∈ D
    · let i : D := ⟨v, hv⟩
      have hmarkv : (d v).high = decide (i ∈ Q) := hmark i
      rw [hmarkv]
      by_cases hq : i ∈ Q
      · have hn : v ∉ image D Q := fun hh => ((low_image D Q v hv).mp hh) hq
        simp [hv, hq, hn]
      · have hp : v ∈ image D Q := (low_image D Q v hv).mpr hq
        simp [hv, hq, hp]
    · have hn : v ∉ image D Q := by
        intro hh
        obtain ⟨i, he, _⟩ := (mem_image D Q v).mp hh
        exact hv (he ▸ i.property)
      simp [hv, hn]
  have hns (i : Low D Q) : (assemble (d i.val.val) (dictionary G ids L Δ input i.val.val)).neighbors =
      (publicGraph G C D R L Q).neighborFinset i.val.val := by
    have hdeg : (ownerGraph G C D R L).degree i.val ≤ Δ := low_degree G C D R L Δ i
    have hfalse : (d i.val.val).high = false :=
      ((hcent i.val).2.1).trans (decide_eq_false (not_lt_of_ge hdeg))
    have hc : (d i.val.val).metadata.owned.input.center = true :=
      (congrArg GeneralCoveringOwners.Input.center (hi i.val.val)).trans
        ((hD i.val.val).trans (decide_eq_true i.val.property))
    change (if (d i.val.val).metadata.owned.input.center && !(d i.val.val).high then
      (d i.val.val).neighbors.filter (fun j => TaggedDictionary.lookup
        (dictionary G ids L Δ input i.val.val) j = some false) else ∅) = _
    rw [hc, hfalse]
    simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
    rw [(hcent i.val).2.2.2 hdeg, neighbor_filter G C D R L Q i]
    change (((ownerGraph G C D R L).neighborFinset i.val).image (Subtype.val : D → V)).filter
      (fun j => TaggedDictionary.lookup (dictionary G ids L Δ input i.val.val) j = some false) =
      (((ownerGraph G C D R L).neighborFinset i.val).filter (fun j => j ∉ Q)).image Subtype.val
    ext v
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, hj, he⟩, hlookup⟩
      have hadj := ((ownerGraph G C D R L).mem_neighborFinset i.val j).mp hj
      have hlookupj : TaggedDictionary.lookup (dictionary G ids L Δ input i.val.val) j.val = some false := by
        rw [he]
        exact hlookup
      have hjfalse : (d j.val).high = false := Option.some.inj ((hlook i.val j hdeg hadj).symm.trans hlookupj)
      have hn : ¬ Δ < (ownerGraph G C D R L).degree j :=
        of_decide_eq_false (((hcent j).2.1).symm.trans hjfalse)
      exact ⟨j, ⟨hj, fun hq => hn ((mem_high G C D R L Δ j).mp hq)⟩, he⟩
    · rintro ⟨j, ⟨hj, hnot⟩, he⟩
      refine ⟨⟨j, hj, he⟩, ?_⟩
      have hn : ¬ Δ < (ownerGraph G C D R L).degree j :=
        fun hh => hnot ((mem_high G C D R L Δ j).mpr hh)
      rw [← he, hlook i.val j hdeg (((ownerGraph G C D R L).mem_neighborFinset i.val j).mp hj),
        (hcent j).2.1, decide_eq_false hn]
  have hnsall (v : V) : (assemble (d v) (dictionary G ids L Δ input v)).neighbors =
      (publicGraph G C D R L Q).neighborFinset v := by
    by_cases hv : v ∈ image D Q
    · obtain ⟨i, he, hnot⟩ := (mem_image D Q v).mp hv
      subst v
      exact hns (⟨i, hnot⟩ : Low D Q)
    · have he : (assemble (d v) (dictionary G ids L Δ input v)).low = false :=
        (hl v).trans (decide_eq_false hv)
      exact (assemble_empty _ _ he).trans (neighbor_outside G C D R L Q v hv).symm
  dsimp only
  rw [encoded_run]
  refine ⟨?_, ?_, hl, hnsall, ?_, ?_, ?_⟩
  · intro v
    exact ⟨hm v, hi v, rfl⟩
  · intro i
    exact (hcent i).2.1
  · intro i j hdeg ha
    exact (hlook i j hdeg ha).trans (congrArg Option.some ((hcent j).2.1))
  · intro v hv
    exact congrArg GeneralCoveringOwnerDiscovery.Output.high (houtside v hv)
  · intro v hv
    apply assemble_empty
    change ((d v).metadata.owned.input.center && !(d v).high) = false
    rcases hv with hn | hc | hh
    · have hnot : v ∉ D := by
        intro hvD
        have he : (some v : Option V) = none :=
          (GeneralCoveringOwners.owner_center C D R hvD).symm.trans hn
        cases he
      simp [hi v, hD v, hnot]
    · simp [hi v, hD v, hc]
    · change (d v).high = true at hh
      simp [hh]

end Paper.GeneralCoveringOwnerVirtualPrepare

#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.assemble_empty
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.rounds
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.maxBits
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.run_program
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.encoded_run
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.metadata_retained
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.private_input_retained
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.mem_image
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.range_eq
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.low_image
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.mem_high
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.low_degree
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.neighbor_filter
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.neighbor_outside
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.public_degree_bound
#print axioms Paper.GeneralCoveringOwnerVirtualPrepare.private_correct
