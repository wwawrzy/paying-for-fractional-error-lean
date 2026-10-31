import Paper.Preliminaries.VirtualSimulationCorrect
import Paper.Preliminaries.TopologyGather

/-! A concrete physical BC program gathers exact bounded-radius topology
in the low-owner graph, using public physical IDs and actual preparation.
The original physical graph may have arbitrarily large degrees. -/
namespace Paper.OwnerTopologyGather
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    Program V (Bool × Bool) (List (TopologyGather.Record V Δ) × OwnerVirtualPrepare.Env V) :=
  .seq (.local fun _ _ s => (s, ()))
    (VirtualSimulation.execute C L Δ (TopologyGather.program C Δ r))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem run_program {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) : (program C L Δ r).run G (fun v => (decide (v ∈ D), decide (v ∈ S))) = fun v =>
      ((TopologyGather.program C Δ r).run (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) (fun _ => ()) v,
        OwnerVirtualCorrect.learned G C D S L Δ v) :=
  VirtualSimulationCorrect.execute_correct G C D S hcover L Δ (TopologyGather.program C Δ r) (fun _ => ())

theorem records {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) (a : TopologyGather.Record V Δ) :
    a ∈ ((program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1 ↔
      ∃ u, ∃ p : (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).Walk v u,
        p.length ≤ r ∧ a = TopologyGather.localData (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) Δ u := by
  rw [run_program G C D S hcover L Δ r]
  exact TopologyGather.records _ C Δ r (PublicOwners.degree_bound G D S L Δ) v a

theorem record_true {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) (a : TopologyGather.Record V Δ)
    (ha : a ∈ ((program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1) :
    ∃ u, ∃ p : (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).Walk v u,
      p.length ≤ r ∧ a.1 = u ∧ a.2.val =
        ((PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u).sort (· ≤ ·) := by
  obtain ⟨u, p, hp, rfl⟩ := (records G C D S hcover L Δ r v a).mp ha
  exact ⟨u, p, hp, rfl, TopologyGather.true_neighbors _ Δ (PublicOwners.degree_bound G D S L Δ) u⟩

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) : (program C L Δ r).rounds = 10 + 4 * r := by
  simp only [program, Program.rounds, VirtualSimulation.execute_rounds, TopologyGather.rounds, Nat.zero_add]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    (program C L Δ r).maxBits ≤ (L + Δ + 4) * (b + (Δ + 1) ^ (r + 1) * (b + 1) + 2) := by
  simp only [program, Program.maxBits, Nat.zero_max]
  apply (VirtualSimulation.execute_maxBits C L Δ (TopologyGather.program C Δ r)).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left (TopologyGather.maxBits C Δ r) b) 2)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ r n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ r).maxBits ≤
      ((L + Δ + 4) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2)) * Nat.clog 2 (n + 2) := by
  simp only [program, Program.maxBits, Nat.zero_max]
  exact VirtualSimulation.execute_logarithmic_bits C L Δ (TopologyGather.program C Δ r) n c
    ((Δ + 1) ^ (r + 1) * (c + 1)) hids (TopologyGather.logarithmic_bits C Δ r c n hids)
end Paper.OwnerTopologyGather
