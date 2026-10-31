import Paper.Preliminaries.VirtualSimulation
import Paper.Owners.Construction.OwnerVirtualCorrect

/-! Full compiler correctness: every virtual local/broadcast/seq program
runs correctly on the actual physical graph after actual ten-round
preparation. No private graph/decoder/neighbor/delivery oracle. -/
namespace Paper.VirtualSimulationCorrect
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance taskAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L Δ : ℕ) :
    DecidableRel (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).Adj := fun _ _ => Classical.propDecidable _

theorem neighbor_lifts (D S : Finset V) (L Δ : ℕ) (v u : V)
    (hu : u ∈ (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset v) :
    ∃ i j : OwnerTasks.Low D (OwnerVirtualFacts.high G D S L Δ),
      (OwnerTasks.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).Adj i j ∧
        i.val.val = v ∧ j.val.val = u := by
  exact (PublicEmbedding.adj_iff (OwnerTasks.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
    (PublicOwners.embedding D _) v u).mp
      ((SimpleGraph.mem_neighborFinset (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) v u).mp hu)

theorem routed_neighbor {A : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode A w)
    (D S : Finset V) (hcover : S ⊆ covered G D) (L Δ : ℕ) (f : V → A) (v u : V)
    (hu : u ∈ (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset v) :
    TaggedDictionary.lookup ((OwnerPayloadRoute.program C P L Δ).run G
      (OwnerPayloadInputs.expected G D S L (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) f) v) u = some (f u) := by
  obtain ⟨i, j, hij, hi, hj⟩ := neighbor_lifts G D S L Δ v u hu
  rw [← hi]
  apply OwnerPayloadRouteCorrect.lookup_correct G C P D S hcover L Δ _ f i.val
    (OwnerVirtualFacts.low_degree G D S L Δ i) u
  · rw [OwnerVirtualFacts.neighbors_image G D S hcover L i.val]
    exact Finset.mem_image.mpr ⟨j.val, (SimpleGraph.mem_neighborFinset (OwnerInteraction.graph G D S L) i.val j.val).mpr hij, hj⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem round_correct {In Out Msg : Type} {b w : ℕ} (C : BitCode V b) (P : BitCode Msg w)
    (D S : Finset V) (hcover : S ⊆ covered G D) (L Δ : ℕ) (R0 : Round V In Out Msg) (s : V → In) :
    (VirtualSimulation.simulateRound C P L Δ R0).run G
      (fun v => (s v, OwnerVirtualCorrect.learned G C D S L Δ v)) = fun v =>
        (eval (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) R0 s v,
          OwnerVirtualCorrect.learned G C D S L Δ v) := by
  let J := PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)
  let E := OwnerVirtualCorrect.learned G C D S L Δ
  let f := fun v => R0.send v (J.neighborFinset v) (s v)
  have hin : (fun v => (⟨(E v).metadata, (E v).low, R0.send v (E v).neighbors (s v)⟩ : OwnerPayloadRoute.Input V Msg)) =
      OwnerPayloadInputs.expected G D S L (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) f := by
    funext v
    dsimp only [OwnerPayloadInputs.expected]
    rw [OwnerVirtualCorrect.metadata_correct, OwnerVirtualCorrect.low_correct G C D S hcover,
      OwnerVirtualCorrect.neighbors_correct G C D S hcover]
  rw [VirtualSimulation.round_run]
  dsimp only
  rw [hin]
  funext v
  refine Prod.ext ?_ rfl
  change R0.update v (E v).neighbors (s v) (fun u =>
    (TaggedDictionary.lookup ((OwnerPayloadRoute.program C P L Δ).run G
      (OwnerPayloadInputs.expected G D S L (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) f) v) u.val).getD
        (R0.send v (E v).neighbors (s v))) =
      R0.update v (J.neighborFinset v) (s v) (fun u => R0.send u.val (J.neighborFinset u.val) (s u.val))
  rw [OwnerVirtualCorrect.neighbors_correct G C D S hcover L Δ v]
  apply congrArg (R0.update v (J.neighborFinset v) (s v))
  funext u
  rw [routed_neighbor G C P D S hcover L Δ f v u.val u.property]
  rfl

theorem translate_correct {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ : ℕ) {In Out : Type} (P : Program V In Out) : ∀ s : V → In,
    (VirtualSimulation.translate C L Δ P).run G (fun v => (s v, OwnerVirtualCorrect.learned G C D S L Δ v)) = fun v =>
      (P.run (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) s v,
        OwnerVirtualCorrect.learned G C D S L Δ v) := by
  induction P with
  | «local» f =>
    intro s
    funext v
    change (f v (OwnerVirtualCorrect.learned G C D S L Δ v).neighbors (s v), _) = _
    rw [OwnerVirtualCorrect.neighbors_correct G C D S hcover]
    rfl
  | broadcast w code R0 =>
    intro s
    exact round_correct G C code D S hcover L Δ R0 s
  | seq P Q ihP ihQ =>
    intro s
    change (VirtualSimulation.translate C L Δ Q).run G
      ((VirtualSimulation.translate C L Δ P).run G (fun v => (s v, OwnerVirtualCorrect.learned G C D S L Δ v))) = _
    rw [ihP s]
    exact ihQ _

theorem execute_correct {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ : ℕ) {In Out : Type} (P : Program V In Out) (s : V → In) :
    (VirtualSimulation.execute C L Δ P).run G (fun v => ((decide (v ∈ D), decide (v ∈ S)), s v)) = fun v =>
      (P.run (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) s v,
        OwnerVirtualCorrect.learned G C D S L Δ v) := by
  change (VirtualSimulation.translate C L Δ P).run G ((Program.local fun _ _ s => (s.2, s.1)).run G
    ((ProgramMemory.carry (OwnerVirtualPrepare.program C L Δ)).run G
      (fun v => ((decide (v ∈ D), decide (v ∈ S)), s v)))) = _
  rw [ProgramMemory.run G (OwnerVirtualPrepare.program C L Δ)]
  exact translate_correct G C D S hcover L Δ P s
end Paper.VirtualSimulationCorrect
