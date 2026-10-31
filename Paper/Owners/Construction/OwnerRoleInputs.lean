import Paper.Owners.Construction.OwnerRoleFrames
import Paper.Owners.Construction.OwnerRoleTaskData
import Paper.Preliminaries.RoleInputList

/-! Literal physical generation of all fixed-metadata roles at actual
possible anchors. Every own input is computed from bounded delivered
frames, private own metadata/cost and public finite parameters. -/
namespace Paper.OwnerRoleInputs
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def metadataCount (Δ k Q T s : ℕ) : ℕ :=
  OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s)

def capacity (L Δ k Q T s : ℕ) : ℕ :=
  ((L + 1) * (Δ + 1) ^ k) * metadataCount Δ k Q T s

def value {b : ℕ} (C : BitCode V b) (Δ r k t Q T s B : ℕ) (hQ : 0 < Q)
    (xs : List (V × OwnerFramePayload.Frame V Δ r)) (env : OwnerVirtualPrepare.Env V)
    (c : Fin (B + 1)) (role : TaskRoleId.Id V (metadataCount Δ k Q T s)) :
    FractionalSearch.Input V B :=
  let a := (ofLex role).1
  let i := (ofLex role).2
  OwnerRoleTaskData.input (OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ a i
    (RootFrameUnion.canonical s a xs)) env.metadata c

def build {b : ℕ} (C : BitCode V b) (Δ r k t Q T s B : ℕ) (hQ : 0 < Q)
    (anchors : Finset V) (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (env : OwnerVirtualPrepare.Env V) (c : Fin (B + 1)) :=
  RoleInputList.rows (TaskRoleId.space anchors (metadataCount Δ k Q T s))
    (value C Δ r k t Q T s B hQ xs env c)

def program {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) :
    Program V ((Bool × Bool) × Fin (B + 1))
      (List (TaskRoleId.Id V (metadataCount Δ k Q T s) × FractionalSearch.Input V B)) :=
  .seq (ProgramMemory.carry (OwnerRoleFrames.program C L Δ r k))
    (.local fun _ _ st => build C Δ r k t Q T s B hQ st.1.1 st.1.2.1 st.1.2.2 st.2)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D S : Finset V)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v : V) :
    (program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v =
      let st := (OwnerRoleFrames.program C L Δ r k).run G
        (fun u => (decide (u ∈ D), decide (u ∈ S))) v
      build C Δ r k t Q T s B hQ st.1 st.2.1 st.2.2 (c v) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (OwnerRoleFrames.program C L Δ r k)]

theorem keys {b : ℕ} (C : BitCode V b) (D S : Finset V)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v : V) :
    TaggedDictionary.keys ((program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v) =
      TaskRoleId.space (RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D S L Δ r v))
        (metadataCount Δ k Q T s) := by
  rw [run_program]
  exact RoleInputList.keys _ _

theorem key_bound {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (hk : k ≤ r) (c : V → Fin (B + 1)) (v : V) :
    (TaggedDictionary.keys ((program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v)).card ≤ capacity L Δ k Q T s := by
  rw [keys, TaskRoleId.card_space]
  exact Nat.mul_le_mul_right _ (OwnerRootFrameCorrect.anchors_card G C D S hcover L Δ r k hk v)

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s B hQ).rounds = 13 + 4 * r := by
  simp only [program, Program.rounds, ProgramMemory.rounds, OwnerRoleFrames.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s B hQ).maxBits = (OwnerRoleFrames.program C L Δ r k).maxBits := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]

end Paper.OwnerRoleInputs
