import Paper.Owners.Construction.OwnerFramePayload
import Paper.Preliminaries.RootPayloadCorrect

/-! Actual physical construction of true topology frames at every relevant
low root: topology gathering followed by three root-payload broadcasts. -/
namespace Paper.OwnerRootFrames
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def routeInput {Δ r : ℕ} (s : OwnerFramePayload.Frame V Δ r × OwnerVirtualPrepare.Env V) :
    OwnerPayloadRoute.Input V (OwnerFramePayload.Frame V Δ r) := ⟨s.2.metadata, s.2.low, s.1⟩

def program {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) : Program V (Bool × Bool)
    ({l : List (V × OwnerFramePayload.Frame V Δ r) // l.length ≤ L + 1} × OwnerVirtualPrepare.Env V) :=
  .seq (OwnerFramePayload.program C L Δ r)
    (.seq (.local fun _ _ s => (routeInput s, s.2))
      (ProgramMemory.carry (RootPayloadRoute.program C (OwnerFramePayload.code C Δ r) L)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

def frame {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ r : ℕ) (v : V) :=
  ((OwnerFramePayload.program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1

theorem run_program {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    (program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v =
      ((RootPayloadRoute.program C (OwnerFramePayload.code C Δ r) L).run G
        (OwnerPayloadInputs.expected G D S L (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
          (frame G C D S L Δ r)) v, OwnerVirtualCorrect.learned G C D S L Δ v) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (RootPayloadRoute.program C (OwnerFramePayload.code C Δ r) L)]
  dsimp only
  have hin : (fun u => routeInput ((OwnerFramePayload.program C L Δ r).run G
      (fun w => (decide (w ∈ D), decide (w ∈ S))) u)) =
      OwnerPayloadInputs.expected G D S L (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
        (frame G C D S L Δ r) := by
    funext u
    unfold routeInput
    rw [OwnerFramePayload.env G C D S hcover L Δ r u,
      OwnerVirtualCorrect.metadata_correct G C D S L Δ u,
      OwnerVirtualCorrect.low_correct G C D S hcover L Δ u]
    rfl
  rw [hin, OwnerFramePayload.env G C D S hcover L Δ r v]

theorem keys {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    TaggedDictionary.keys (((program C L Δ r).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).val =
      RoleAnchorGeometry.roots G D S L v ∩ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ) := by
  rw [run_program G C D S hcover L Δ r v]
  exact RootPayloadCorrect.keys G C (OwnerFramePayload.code C Δ r) D S hcover L _ _ v

theorem consistent {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    TaggedDictionary.Consistent (frame G C D S L Δ r) (((program C L Δ r).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).val := by
  rw [run_program G C D S hcover L Δ r v]
  exact RootPayloadCorrect.consistent G C (OwnerFramePayload.code C Δ r) D S hcover L _ _ v

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    (program C L Δ r).rounds = 13 + 4 * r := by
  simp only [program, Program.rounds, ProgramMemory.rounds, OwnerFramePayload.rounds,
    RootPayloadRoute.rounds]
  omega

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    (program C L Δ r).maxBits ≤ max (OwnerTopologyGather.program C L Δ r).maxBits
      (b + OwnerFramePayload.capacity Δ r * (b + Δ * (b + 1) + 1) + 1) := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max,
    OwnerFramePayload.maxBits]
  exact max_le_max (le_refl _) (RootPayloadRoute.maxBits C (OwnerFramePayload.code C Δ r) L)

end Paper.OwnerRootFrames
