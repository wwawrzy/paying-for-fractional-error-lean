import Paper.Partitions.Local.PriorityBoundaryBroadcast
import Paper.Partitions.Local.ClosedNeighborBalls
import Paper.Preliminaries.NeighborLocality
import Paper.Owners.Construction.OwnerVirtualFacts

/-! A finite-seed, bounded-output virtual program for boundary averaging.
At active low roots, all reachable public vertices are active; local
all-true input flags thus give exactly the actual active-image boundary. -/
namespace Paper.LowBoundarySeedScore
open BroadcastModel
variable {V : Type} [LinearOrder V]

def score (b : Bool) : Fin 2 := ⟨b.toNat, by cases b <;> decide⟩

def program {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    Program V (PriorityPartitionBroadcast.Table Δ k Q n) (Fin 2) :=
  .seq (.local fun _ _ s => (true, s))
    (.seq (PriorityBoundaryBroadcast.program C Δ k t Q n hQ) (.local fun _ _ b => score b))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem root_correct {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Q n : ℕ) (hQ : 0 < Q)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q n) (v : V)
    (hv : v ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) :
    (((program C Δ k t Q n hQ).run
      (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) ζ v).val) =
        (decide (v ∈ BoundaryOwners.vertices
          (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
          (PriorityPartition.partition (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
            k hk (1 / (t : ℝ)) (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) n
            (PriorityNormalization.localSeed (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
              Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts)).toNat := by
  have hh := NeighborLocality.input_locality (PriorityBoundaryBroadcast.program C Δ k t Q n hQ)
    (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u)
    (fun u => (true, ζ u))
    (fun u => (decide (u ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)), ζ u)) v
    (fun u hu => by
      dsimp only
      rw [decide_eq_true (ClosedNeighborBalls.owner_subset G D S L _ v hv _ hu)])
  rw [NeighborInterpreter.run_graph, NeighborInterpreter.run_graph] at hh
  change ((PriorityBoundaryBroadcast.program C Δ k t Q n hQ).run
    (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) (fun u => (true, ζ u)) v).toNat = _
  rw [hh]
  exact congrArg Bool.toNat (PriorityBoundaryBroadcast.correct
    (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) C Δ k hk t ht Q n hQ
    (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) ζ (PublicOwners.degree_bound G D S L Δ) v)

theorem rounds {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C Δ k t Q n hQ).rounds = n * (3 * k + 1) + 1 := by
  simp only [program, Program.rounds, Nat.zero_add, Nat.add_zero, PriorityBoundaryBroadcast.rounds]

theorem maxBits {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C Δ k t Q n hQ).maxBits = (PriorityBoundaryBroadcast.program C Δ k t Q n hQ).maxBits := by
  simp only [program, Program.maxBits, Nat.zero_max, Nat.max_zero]
end Paper.LowBoundarySeedScore
