import Paper.Solver.LocalSearch.GeneralCoveringOwnerFramePartitionCounts
import Paper.Owners.Construction.OwnerRoleMetadata
import Paper.Preliminaries.FiniteSubsetCode
import Paper.Solver.LocalSearch.GeneralCoveringFractional

/-! Executable full-task decoder for actual arbitrary-covering metadata.
A frame of radius k plus the partition radius determines every boundary
flag needed inside a candidate owner part. Original incidence lists and
cost are read only from the physical vertex's retained private state.
The decoder does not enumerate a physical dependency ball. -/
namespace Paper.GeneralCoveringOwnerFrameTaskData
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def frameRadius (k n : ℕ) : ℕ := k + GeneralCoveringOwnerFramePartition.radius k n
def partSlots (Δ k : ℕ) : ℕ := (Δ + 1) ^ k
def frameSlots (Δ k n : ℕ) : ℕ := (Δ + 1) ^ frameRadius k n
def metadataCount (Δ k b n : ℕ) : ℕ :=
  OwnerRoleMetadata.count (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n)

abbrev Metadata (Δ k b n : ℕ) := Fin (metadataCount Δ k b n)

structure Task (V : Type) where
  owners : Finset V
  boundary : V → Bool
  valid : Bool

def coins (Δ k b n : ℕ) (i : Metadata Δ k b n) (u : Fin (frameSlots Δ k n)) :
    ActiveFiniteBitPartition.Bits Δ k b n := fun j =>
  (PriorityTableCode.masks b).symm
    (OwnerRoleMetadata.table (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i u j)

/-- Encode actual Boolean tables through the existing computable finite code. -/
def encode (Δ k b n : ℕ) (mask : Fin (partSlots Δ k) → Bool)
    (ω : Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) : Metadata Δ k b n :=
  OwnerRoleMetadata.equiv (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n)
    (mask, fun j =>
      let p := finProdFinEquiv.symm j
      let q := finProdFinEquiv.symm p.2
      PriorityTableCode.masks b (ω p.1 (q.1, (PriorityTableCode.masks (partSlots Δ k)).symm q.2)))

theorem mask_encode (Δ k b n : ℕ) (mask : Fin (partSlots Δ k) → Bool)
    (ω : Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) :
    OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) (encode Δ k b n mask ω) = mask :=
  OwnerRoleMetadata.mask_encode _ _ _ _ _

theorem coins_encode (Δ k b n : ℕ) (mask : Fin (partSlots Δ k) → Bool)
    (ω : Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) :
    coins Δ k b n (encode Δ k b n mask ω) = ω := by
  funext u j
  simp only [coins, OwnerRoleMetadata.table, encode, OwnerRoleMetadata.configuration_encode,
    Equiv.symm_apply_apply]

theorem encode_decode (Δ k b n : ℕ) (i : Metadata Δ k b n) :
    encode Δ k b n
      (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i)
      (coins Δ k b n i) = i := by
  unfold encode coins OwnerRoleMetadata.table
  simp only [Prod.eta, Equiv.apply_symm_apply]
  exact OwnerRoleMetadata.encode_decode _ _ _ _ i

/-- Computable bijection: every mask and every Boolean coin array occurs once. -/
def sourceEquiv (Δ k b n : ℕ) : Metadata Δ k b n ≃
    (Fin (partSlots Δ k) → Bool) ×
      (Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) where
  toFun i := (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i, coins Δ k b n i)
  invFun p := encode Δ k b n p.1 p.2
  left_inv := encode_decode Δ k b n
  right_inv p := Prod.ext (mask_encode Δ k b n p.1 p.2) (coins_encode Δ k b n p.1 p.2)

/-- Exact weighted enumeration, grouping metadata by its actual coin array. -/
theorem sum_metadata (Δ k b n : ℕ)
    (f : (Fin (partSlots Δ k) → Bool) →
      (Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) → ℕ) :
    (∑ i : Metadata Δ k b n,
      f (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i) (coins Δ k b n i)) =
      ∑ ω : Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n,
        ∑ mask : Fin (partSlots Δ k) → Bool, f mask ω := by
  calc
    _ = ∑ p : (Fin (partSlots Δ k) → Bool) ×
        (Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n), f p.1 p.2 :=
      Fintype.sum_equiv (sourceEquiv Δ k b n) _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

def seeds (Δ k b n : ℕ) (i : Metadata Δ k b n) (xs : List (TopologyGather.Record V Δ)) :
    List (V × ActiveFiniteBitPartition.Input Δ k b n) :=
  if h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n then
    LocalSeedRecords.records (GeneralCoveringOwnerFramePartition.addresses xs) h
      (fun u => (true, coins Δ k b n i u)) else []

def view {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (i : Metadata Δ k b n)
    (xs : List (TopologyGather.Record V Δ)) (u : V) : Finset V × Bool :=
  FrameInterpreter.evaluate (ActiveFiniteBitPartition.program I Δ k t b n) xs (seeds Δ k b n i xs)
    (true, GeneralCoveringOwnerFramePartition.zeroBits Δ k b n) u

def compute {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (a : V) (i : Metadata Δ k b n)
    (xs : List (TopologyGather.Record V Δ)) : Task V :=
  let l := (NeighborBalls.ball (FrameInterpreter.neighbors xs) a k).sort (· ≤ ·)
  let mask := OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i
  let S := FiniteSubsetCode.decode l (partSlots Δ k) mask
  let f := view I Δ k t b n i xs
  ⟨S, fun u => (f u).2,
    decide ((GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n ∧
      mask = FiniteSubsetCode.encode l (partSlots Δ k) S ∧ S.card ≤ k ∧
      MaskedMinimum.minimum S = some a ∧ (f a).1 = S)⟩

/-- Optional owners are inspected without inventing a default physical ID. -/
def owned (d : Task V) (m : GeneralCoveringOwnerSupport.State V) : Bool :=
  (m.owned.owner.map (fun u => decide (u ∈ d.owners))).getD false

def interior (d : Task V) (m : GeneralCoveringOwnerSupport.State V) : Bool :=
  (m.owned.owner.map (fun u => decide (u ∈ d.owners) && !d.boundary u)).getD false

def input {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    GeneralCoveringFractional.Input V B :=
  ⟨d.valid && (owned d m || (m.admissible && !m.heavy && decide ((m.support ∩ d.owners).Nonempty))),
    c, d.valid && m.residual && interior d m,
    m.owned.input.candidates, m.owned.input.targets⟩

theorem cost_retained {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    (input d m c).cost = c := rfl

theorem candidates_retained {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    (input d m c).candidates = m.owned.input.candidates := rfl

theorem targets_retained {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    (input d m c).targets = m.owned.input.targets := rfl

theorem invalid {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1))
    (h : d.valid = false) : (input d m c).active = false ∧ (input d m c).demand = false := by
  simp only [input, h, Bool.false_and, and_self]

theorem owned_iff (d : Task V) (m : GeneralCoveringOwnerSupport.State V) :
    owned d m = true ↔ ∃ u ∈ d.owners, m.owned.owner = some u := by
  cases h : m.owned.owner with
  | none => simp [owned, h]
  | some u => simp [owned, h]

theorem interior_iff (d : Task V) (m : GeneralCoveringOwnerSupport.State V) :
    interior d m = true ↔ ∃ u ∈ d.owners, d.boundary u = false ∧ m.owned.owner = some u := by
  cases h : m.owned.owner with
  | none => simp [interior, h]
  | some u => simp [interior, h]

/-- The decoder's complete Boolean contract before interpreting a graph. -/
theorem active_iff {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    (input d m c).active = true ↔ d.valid = true ∧
      ((∃ u ∈ d.owners, m.owned.owner = some u) ∨
        (m.admissible = true ∧ m.heavy = false ∧ (m.support ∩ d.owners).Nonempty)) := by
  simp only [input, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, owned_iff]
  simp only [and_assoc]

theorem demand_iff {B : ℕ} (d : Task V) (m : GeneralCoveringOwnerSupport.State V) (c : Fin (B + 1)) :
    (input d m c).demand = true ↔ d.valid = true ∧ m.residual = true ∧
      ∃ u ∈ d.owners, d.boundary u = false ∧ m.owned.owner = some u := by
  simp only [input, Bool.and_eq_true, interior_iff]
  tauto

/-- One metadata configuration reads only the supplied finite frame. -/
theorem same_frame {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (a : V) (i : Metadata Δ k b n)
    (xs ys : List (TopologyGather.Record V Δ)) (h : xs = ys) :
    compute I Δ k t b n a i xs = compute I Δ k t b n a i ys := by rw [h]

/-- The precise finite seed list seen by the existing frame interpreter. -/
theorem seeds_records (Δ k b n : ℕ) (i : Metadata Δ k b n) (xs : List (TopologyGather.Record V Δ))
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n) :
    seeds Δ k b n i xs = LocalSeedRecords.base (GeneralCoveringOwnerFramePartition.addresses xs)
      (fun j => (true, coins Δ k b n i (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h j))) := by
  simp only [seeds, dif_pos h, LocalSeedRecords.records]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- This is the exact same global assignment at all queried owner IDs.
The proof uses only the supplied frame, not a physical graph-size bound. -/
theorem view_restricted {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (i : Metadata Δ k b n)
    (xs : List (TopologyGather.Record V Δ)) (U : Finset V) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (u : V) (hsize : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n)
    (htrue : ∀ p ∈ xs, p.2.val.toFinset = G.neighborFinset p.1)
    (hcover : NeighborBalls.ball (fun w => G.neighborFinset w) u
      (ActiveFiniteBitPartition.program I Δ k t b n).rounds ⊆ TaggedDictionary.keys xs)
    (hlow : (GeneralCoveringOwnerFramePartition.addresses xs).toFinset ⊆ U)
    (hcoins : ∀ j, coins Δ k b n i (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) hsize j) =
      β ((GeneralCoveringOwnerFramePartition.addresses xs).get j)) :
    view I Δ k t b n i xs u =
      (ActiveFiniteBitPartition.program I Δ k t b n).runEncoded G (fun w => (decide (w ∈ U), β w)) u := by
  let l := GeneralCoveringOwnerFramePartition.addresses xs
  let σ := fun w => (decide (w ∈ U), β w)
  have hs : seeds Δ k b n i xs = LocalSeedRecords.base l (fun j => σ (l.get j)) := by
    rw [seeds_records Δ k b n i xs hsize]
    apply congrArg (LocalSeedRecords.base l)
    funext j
    apply Prod.ext
    · have hj : l.get j ∈ U := hlow (List.mem_toFinset.mpr (l.get_mem j))
      change true = decide (l.get j ∈ U)
      exact (decide_eq_true hj).symm
    · exact hcoins j
  have hl : NeighborBalls.ball (fun w => G.neighborFinset w) u
      (ActiveFiniteBitPartition.program I Δ k t b n).rounds ⊆ l.toFinset := by
    simpa only [l, GeneralCoveringOwnerFramePartition.addresses, Finset.sort_toFinset] using hcover
  unfold view
  rw [hs]
  exact (LocalSeedRecords.evaluate_base G (ActiveFiniteBitPartition.program I Δ k t b n) xs l σ
    (true, GeneralCoveringOwnerFramePartition.zeroBits Δ k b n) u htrue hcover hl).trans
    (congrFun (Program.runEncoded_eq_run G (ActiveFiniteBitPartition.program I Δ k t b n) σ) u).symm

private theorem bool_of_iff (z : Bool) (p : Prop) [Decidable p] (h : z = true ↔ p) : z = decide p := by
  cases z <;> simp_all

/-- Interpretation of original-C task vertices from the retained local state. -/
theorem active_correct (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (S : Finset (Low D Q)) (d : Task V) (m : GeneralCoveringOwnerSupport.State V)
    {B : ℕ} (c : Fin (B + 1)) (v : V) (hv : d.valid = true)
    (hS : d.owners = GeneralCoveringOwnerRoleFrames.partIds D Q S)
    (ho : m.owned.owner = GeneralCoveringOwners.owner C D R v)
    (had : m.admissible = decide (v ∈ CoveringSupport.admissible C R))
    (hh : m.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L))
    (hs : m.support = GeneralCoveringOwnerSupport.support G C D R v) :
    (input d m c).active = decide (v ∈ vertices G C D R L Q S) := by
  apply bool_of_iff
  rw [active_iff, hv]
  simp only [true_and, ho, had, hh, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro (⟨u, hu, howner⟩ | ⟨hadm, hheavy, u, hu⟩)
    · rw [hS] at hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_filter.mpr ⟨GeneralCoveringOwners.owner_domain C D R howner, howner⟩⟩)
    · obtain ⟨huSup, huS⟩ := Finset.mem_inter.mp hu
      rw [hS] at huS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huS
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi,
        (mem_lightSupport G C D R L v _).mpr ⟨hadm, hheavy, hs ▸ huSup⟩⟩)
  · intro hmem
    rcases Finset.mem_union.mp hmem with hstar | hlight
    · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hstar
      exact Or.inl ⟨i.val.val, hS.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩, (Finset.mem_filter.mp hvi).2⟩
    · obtain ⟨i, hi, hil⟩ := (Finset.mem_filter.mp hlight).2
      obtain ⟨hadm, hheavy, hsup⟩ := (mem_lightSupport G C D R L v _).mp hil
      exact Or.inr ⟨hadm, hheavy, i.val.val, Finset.mem_inter.mpr
        ⟨hs.symm ▸ hsup, hS.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩

/-- Only boundary values at owners of this part enter its original-C rows. -/
theorem demand_correct (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (S Bdy : Finset (Low D Q)) (d : Task V) (m : GeneralCoveringOwnerSupport.State V)
    {B : ℕ} (c : Fin (B + 1)) (v : V) (hv : d.valid = true)
    (hS : d.owners = GeneralCoveringOwnerRoleFrames.partIds D Q S)
    (ho : m.owned.owner = GeneralCoveringOwners.owner C D R v)
    (hr : m.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G C D R L))
    (hb : ∀ i ∈ S, d.boundary i.val.val = decide (i ∈ Bdy)) :
    (input d m c).demand = decide (v ∈ demands G C D R L Q S Bdy) := by
  apply bool_of_iff
  rw [demand_iff, hv]
  simp only [true_and, hr, ho, decide_eq_true_eq]
  constructor
  · rintro ⟨hres, u, hu, hbound, howner⟩
    rw [hS] at hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hn : i ∉ Bdy := by simpa only [hb i hi, decide_eq_false_iff_not] using hbound
    exact Finset.mem_filter.mpr ⟨hres, i, hi, hn, howner⟩
  · intro hmem
    obtain ⟨hres, i, hi, hn, howner⟩ := Finset.mem_filter.mp hmem
    exact ⟨hres, i.val.val, hS.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      by simpa only [hb i hi, decide_eq_false_iff_not] using hn, howner⟩

end Paper.GeneralCoveringOwnerFrameTaskData

#print axioms Paper.GeneralCoveringOwnerFrameTaskData.cost_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.candidates_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.targets_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.invalid
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.owned_iff
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.interior_iff
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.active_iff
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.demand_iff
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.same_frame
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.seeds_records

#print axioms Paper.GeneralCoveringOwnerFrameTaskData.mask_encode
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.coins_encode
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.view_restricted

#print axioms Paper.GeneralCoveringOwnerFrameTaskData.active_correct
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.demand_correct

#print axioms Paper.GeneralCoveringOwnerFrameTaskData.encode_decode
#print axioms Paper.GeneralCoveringOwnerFrameTaskData.sourceEquiv

#print axioms Paper.GeneralCoveringOwnerFrameTaskData.sum_metadata
