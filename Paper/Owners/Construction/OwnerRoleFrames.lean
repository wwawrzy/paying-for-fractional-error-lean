import Paper.Owners.Construction.OwnerRootFrameCorrect

/-! Actual per-node role anchors and canonical finite frames, computed
only from delivered root packets. Bounds and common-frame semantics follow. -/
namespace Paper.OwnerRoleFrames
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (L Δ r k : ℕ) :
    Program V (Bool × Bool)
      (Finset V × (List (V × OwnerFramePayload.Frame V Δ r) × OwnerVirtualPrepare.Env V)) :=
  .seq (OwnerRootFrames.program C L Δ r)
    (.local fun _ _ s => (RootFrameUnion.anchors k s.1.val, (s.1.val, s.2)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ r k : ℕ) (v : V) :
    ((program C L Δ r k).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1 =
      RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D S L Δ r v) := rfl

theorem key_bound {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r) (v : V) :
    (((program C L Δ r k).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).card ≤
      (L + 1) * (Δ + 1) ^ k :=
  OwnerRootFrameCorrect.anchors_card G C D S hcover L Δ r k hk v

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r k : ℕ) :
    (program C L Δ r k).rounds = 13 + 4 * r := by
  simp only [program, Program.rounds, OwnerRootFrames.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r k : ℕ) :
    (program C L Δ r k).maxBits = (OwnerRootFrames.program C L Δ r).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ r k n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ r k).maxBits ≤
      max ((L + Δ + 4) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
        (c + OwnerFramePayload.capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (n + 2) := by
  rw [maxBits]
  apply (OwnerRootFrames.maxBits C L Δ r).trans
  apply max_le
  · exact (OwnerTopologyGather.logarithmic_bits C L Δ r n c hids).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hlog : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + 1 ≤ (c + 1) * Nat.clog 2 (n + 2) := by nlinarith
  have hd := Nat.mul_le_mul_left Δ hb
  have hinner : b + Δ * (b + 1) + 1 ≤ (c + Δ * (c + 1) + 1) * Nat.clog 2 (n + 2) := by
    nlinarith
  have houter := Nat.mul_le_mul_left (OwnerFramePayload.capacity Δ r) hinner
  exact (by nlinarith : b + OwnerFramePayload.capacity Δ r * (b + Δ * (b + 1) + 1) + 1 ≤
    (c + OwnerFramePayload.capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (n + 2)).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))

end Paper.OwnerRoleFrames
