import Paper.Preliminaries.OwnedReportNeighborhood
import Paper.Owners.Construction.OwnerMetadataCorrect
import Paper.Owners.Construction.OwnerNeighborReports
import Paper.Preliminaries.HighDegreeCut

/-! Two additional real broadcasts discover bounded owner neighborhoods
and high-degree flags. Capacity Δ+1 implements the strict threshold Δ<deg. -/
namespace Paper.OwnerDiscoveryBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

def prepareSupport : Program V (OwnerMetadataBroadcast.State V) (Finset V × OwnerMetadataBroadcast.State V) :=
  .local fun _ _ s => (s.support, s)

def makeReport (Δ : ℕ) : Program V (Finset V × OwnerMetadataBroadcast.State V) (OwnedReportNeighborhood.Report V) :=
  .local fun _ _ s => ⟨s.2.owner, s.2.remaining, PrefixSet.take (Δ + 1) (s.1.erase s.2.owner)⟩

def finish (Δ : ℕ) : Program V (Finset V) (Finset V × Bool) :=
  .local fun _ _ s => let ids := PrefixSet.take (Δ + 1) s; (ids, decide (Δ < ids.card))

def discover {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : Program V (OwnerMetadataBroadcast.State V) (Finset V × Bool) :=
  .seq prepareSupport (.seq (ProgramMemory.carry (SetNeighborhood.program C L))
    (.seq (makeReport Δ) (.seq (OwnedReportNeighborhood.program C (Δ + 1)) (finish Δ))))

def program {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : Program V (Bool × Bool) (Finset V × Bool) :=
  .seq (OwnerMetadataBroadcast.program C L) (discover C L Δ)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_discover {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → OwnerMetadataBroadcast.State V) :
    (discover C L Δ).run G s = fun v =>
      let unionAt := (SetNeighborhood.program C L).run G (fun u => (s u).support)
      let reports := fun u => (⟨(s u).owner, (s u).remaining,
        PrefixSet.take (Δ + 1) ((unionAt u).erase (s u).owner)⟩ : OwnedReportNeighborhood.Report V)
      let ids := PrefixSet.take (Δ + 1) ((OwnedReportNeighborhood.program C (Δ + 1)).run G reports v)
      (ids, decide (Δ < ids.card)) := by
  change (finish Δ).run G ((OwnedReportNeighborhood.program C (Δ + 1)).run G ((makeReport Δ).run G
    ((ProgramMemory.carry (SetNeighborhood.program C L)).run G (fun u => ((s u).support, s u))))) = _
  rw [ProgramMemory.run G (SetNeighborhood.program C L)]
  rfl

theorem discover_rounds {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : (discover C L Δ).rounds = 2 := rfl

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : (program C L Δ).rounds = 6 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) :
    (program C L Δ).maxBits ≤ (L + Δ + 2) * (b + 1) := by
  simp only [program, discover, prepareSupport, makeReport, finish, Program.maxBits, ProgramMemory.maxBits,
    OwnerMetadataBroadcast.maxBits, SetNeighborhood.maxBits, OwnedReportNeighborhood.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le
  · nlinarith
  · apply max_le <;> nlinarith

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ).maxBits ≤ ((L + Δ + 2) * (c + 1)) * Nat.clog 2 (n + 2) := by
  apply (maxBits C L Δ).trans
  have h := Nat.mul_le_mul_left (L + Δ + 2) (BroadcastModel.logarithmic_message_budget n b c hids).1
  simpa only [Nat.mul_assoc] using h
end Paper.OwnerDiscoveryBroadcast
