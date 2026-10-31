import Paper.Owners.Construction.OwnerDiscoveryCorrect
import Paper.Owners.Construction.OwnerPayloadRouteCorrect

/-! Actual ten-round preparation of private low-owner virtual-neighbor
metadata. High flags are routed using the proved four-round payload code;
only low centers retain their filtered exact neighbor list. -/
namespace Paper.OwnerVirtualPrepare
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Env (V : Type) where
  metadata : OwnerMetadataBroadcast.State V
  high : Bool
  low : Bool
  neighbors : Finset V

def assemble (m : OwnerMetadataBroadcast.State V) (info : Finset V × Bool) (xs : List (V × Bool)) : Env V :=
  let low := m.center && !info.2
  ⟨m, info.2, low, if low then info.1.filter (fun u => TaggedDictionary.lookup xs u = some false) else ∅⟩

def duplicate : Program V (OwnerMetadataBroadcast.State V)
    (OwnerMetadataBroadcast.State V × OwnerMetadataBroadcast.State V) := .local fun _ _ s => (s, s)

def prepareRoute : Program V ((Finset V × Bool) × OwnerMetadataBroadcast.State V)
    (OwnerPayloadRoute.Input V Bool × ((Finset V × Bool) × OwnerMetadataBroadcast.State V)) :=
  .local fun _ _ s => (⟨s.2, s.2.center, s.1.2⟩, s)

def finish : Program V (List (V × Bool) × ((Finset V × Bool) × OwnerMetadataBroadcast.State V)) (Env V) :=
  .local fun _ _ s => assemble s.2.2 s.2.1 s.1

def program {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : Program V (Bool × Bool) (Env V) :=
  .seq (OwnerMetadataBroadcast.program C L) (.seq duplicate
    (.seq (ProgramMemory.carry (OwnerDiscoveryBroadcast.discover C L Δ)) (.seq prepareRoute
      (.seq (ProgramMemory.carry (OwnerPayloadRoute.program C BitCode.bool L Δ)) finish))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def base {b : ℕ} (C : BitCode V b) (L : ℕ) (s : V → Bool × Bool) :=
  (OwnerMetadataBroadcast.program C L).run G s

def info {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → Bool × Bool) :=
  (OwnerDiscoveryBroadcast.discover C L Δ).run G (base G C L s)

def routeInput {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → Bool × Bool) (v : V) : OwnerPayloadRoute.Input V Bool :=
  ⟨base G C L s v, (base G C L s v).center, (info G C L Δ s v).2⟩

def dictionary {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → Bool × Bool) :=
  (OwnerPayloadRoute.program C BitCode.bool L Δ).run G (routeInput G C L Δ s)

theorem run_program {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → Bool × Bool) :
    (program C L Δ).run G s = fun v => assemble (base G C L s v) (info G C L Δ s v) (dictionary G C L Δ s v) := by
  change finish.run G ((ProgramMemory.carry (OwnerPayloadRoute.program C BitCode.bool L Δ)).run G
    (prepareRoute.run G ((ProgramMemory.carry (OwnerDiscoveryBroadcast.discover C L Δ)).run G
      (fun u => (base G C L s u, base G C L s u))))) = _
  rw [ProgramMemory.run G (OwnerDiscoveryBroadcast.discover C L Δ)]
  change finish.run G ((ProgramMemory.carry (OwnerPayloadRoute.program C BitCode.bool L Δ)).run G
    (fun u => (routeInput G C L Δ s u, (info G C L Δ s u, base G C L s u)))) = _
  rw [ProgramMemory.run G (OwnerPayloadRoute.program C BitCode.bool L Δ)]
  rfl

theorem metadata_preserved {b : ℕ} (C : BitCode V b) (L Δ : ℕ) (s : V → Bool × Bool) (v : V) :
    ((program C L Δ).run G s v).metadata = base G C L s v := by
  rw [run_program]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ : ℕ) : (program C L Δ).rounds = 10 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ : ℕ) :
    (program C L Δ).maxBits ≤ (L + Δ + 4) * (b + 2) := by
  simp only [program, duplicate, prepareRoute, finish, Program.maxBits, ProgramMemory.maxBits,
    OwnerMetadataBroadcast.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le
  · nlinarith
  · apply max_le
    · have hd : (OwnerDiscoveryBroadcast.discover C L Δ).maxBits ≤ (L + Δ + 2) * (b + 1) :=
        (le_max_right (OwnerMetadataBroadcast.program C L).maxBits _).trans (OwnerDiscoveryBroadcast.maxBits C L Δ)
      exact hd.trans (by nlinarith)
    · exact (OwnerPayloadRoute.maxBits C BitCode.bool L Δ).trans (by nlinarith)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ).maxBits ≤ ((L + Δ + 4) * (c + 2)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + 2 ≤ (c + 2) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits C L Δ).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 4) hb
end Paper.OwnerVirtualPrepare
