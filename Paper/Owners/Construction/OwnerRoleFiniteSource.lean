import Paper.Owners.Construction.OwnerRoleScoreProjection

/-! Factor the genuine physical role score through only the finite used
priority records. This is a proof of dependence, not a local simulation of
the possibly large physical task graph. -/
namespace Paper.OwnerRoleFiniteSource
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def addresses (D R : Finset V) (L Δ s : ℕ) (anchor : V) : List V :=
  OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D R L Δ s anchor)

def fallback (Δ k Q T : ℕ) (hQ : 0 < Q) : PriorityPartitionBroadcast.Table Δ k Q T := fun _ => ⟨0, hQ⟩

noncomputable def role (D R : Finset V) (L Δ k Q T s : ℕ) (hQ : 0 < Q) (anchor : V)
    (mask : Fin ((Δ + 1) ^ k) → Bool) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s) :=
  TaskRoleId.make anchor (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ
    (addresses G D R L Δ s anchor) ζ mask)

noncomputable def fromRecords {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v anchor : V)
    (mask : Fin ((Δ + 1) ^ k) → Bool) (ys : List (V × PriorityPartitionBroadcast.Table Δ k Q T)) : ℝ :=
  (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
    (role G D R L Δ k Q T s hQ anchor mask
      (FrameInterpreter.inputs ys (fallback Δ k Q T hQ))) : ℝ)

theorem factor {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V) (mask : Fin ((Δ + 1) ^ k) → Bool)
    (ω : Fin ((Δ + 1) ^ s) → PriorityPartitionBroadcast.Table Δ k Q T) :
    (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (TaskRoleId.make anchor (RoleTableEncoding.pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) mask ω)) : ℝ) =
      fromRecords G C D R L Δ r k t Q T s a B q M hQ c v anchor mask
        (LocalSeedRecords.records (addresses G D R L Δ s anchor)
          (CanonicalRoleFrame.addresses_length G D R L Δ s anchor) ω) := by
  let l := addresses G D R L Δ s anchor
  let hF := CanonicalRoleFrame.addresses_length G D R L Δ s anchor
  let ys := LocalSeedRecords.records l hF ω
  let ζ := FrameInterpreter.inputs ys (fallback Δ k Q T hQ)
  let i := RoleTableEncoding.pack ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) mask ω
  have hl : l.Nodup := by
    unfold l addresses OwnerRoleTaskData.addresses
    exact Finset.sort_nodup _ _
  have hζ : ∀ j : Fin l.length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i (LocalSeedRecords.slot l hF j) = ζ (l.get j) := by
    intro j
    rw [RoleTableEncoding.table_pack]
    exact (LocalSeedExtension.inputs_get l hl
      (fun j => ω (LocalSeedRecords.slot l hF j)) (fallback Δ k Q T hQ) j).symm
  have hh := OwnerRoleScoreProjection.project_eq G C D R hcover L Δ r k t Q T s a B q M hQ hks c v anchor i ζ hζ
  change OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) =
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (TaskRoleId.make anchor (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ l ζ
        (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i))) at hh
  rw [RoleTableEncoding.mask_pack] at hh
  exact congrArg (fun n : ℕ => (n : ℝ)) hh

theorem global {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V) (mask : Fin ((Δ + 1) ^ k) → Bool)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    fromRecords G C D R L Δ r k t Q T s a B q M hQ c v anchor mask
      (LocalSeedRecords.base (addresses G D R L Δ s anchor) (fun j => ζ ((addresses G D R L Δ s anchor).get j))) =
      (OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
        (role G D R L Δ k Q T s hQ anchor mask ζ) : ℝ) := by
  let l := addresses G D R L Δ s anchor
  let hF := CanonicalRoleFrame.addresses_length G D R L Δ s anchor
  let ys := LocalSeedRecords.base l (fun j => ζ (l.get j))
  let ζ' := FrameInterpreter.inputs ys (fallback Δ k Q T hQ)
  let i := OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ l ζ mask
  have hζ' : ∀ j : Fin l.length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i (LocalSeedRecords.slot l hF j) = ζ' (l.get j) := by
    intro j
    rw [OwnerRoleConfigProjection.table_project]
    exact (LocalSeedRecords.inputs_base l ζ (fallback Δ k Q T hQ) (l.get j) (List.get_mem _ _)).symm
  have hh := OwnerRoleScoreProjection.project_eq G C D R hcover L Δ r k t Q T s a B q M hQ hks c v anchor i ζ' hζ'
  change OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) =
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (TaskRoleId.make anchor (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ l ζ'
        (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i))) at hh
  rw [OwnerRoleConfigProjection.mask_project] at hh
  exact congrArg (fun n : ℕ => (n : ℝ)) hh.symm

end Paper.OwnerRoleFiniteSource
