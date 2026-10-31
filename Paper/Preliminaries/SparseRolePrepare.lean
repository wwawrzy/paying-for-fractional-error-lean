import Paper.Preliminaries.RoleDictionary
import Paper.Averaging.Tasks.MaskedTaskGraph

/-! Actual one-round sparse-role discovery. Only a fixed number of role
IDs per physical vertex is sent, irrespective of total global role count. -/
namespace Paper.SparseRolePrepare
open BroadcastModel
variable {V R : Type} [DecidableEq V] [LinearOrder R]

structure Env (V R : Type) where
  roles : Finset R
  neighbors : R → Finset V

def program {b : ℕ} (C : BitCode R b) (K : ℕ) : Program V (Finset R) (Env V R) :=
  .broadcast (K * (b + 1)) (ListPacket.bounded C K) {
    send := fun _ _ s => ListPacket.truncate K (s.sort (· ≤ ·))
    update := fun _ N s incoming => ⟨s, fun r =>
      (N.attach.filter (fun u => r ∈ (incoming u).val)).image Subtype.val⟩ }

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def vertices (roles : V → Finset R) (r : R) : Finset V := Finset.univ.filter (fun v => r ∈ roles v)

theorem mem_vertices (roles : V → Finset R) (r : R) (v : V) : v ∈ vertices roles r ↔ r ∈ roles v := by
  simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]

def learned {b : ℕ} (C : BitCode R b) (K : ℕ) (roles : V → Finset R) : V → Env V R :=
  (program C K).run G roles

theorem own_roles {b : ℕ} (C : BitCode R b) (K : ℕ) (roles : V → Finset R) (v : V) :
    (learned G C K roles v).roles = roles v := rfl

theorem neighbor_filter {b : ℕ} (C : BitCode R b) (K : ℕ) (roles : V → Finset R)
    (hK : ∀ v, (roles v).card ≤ K) (v : V) (r : R) :
    (learned G C K roles v).neighbors r = G.neighborFinset v ∩ vertices roles r := by
  have hl : ∀ u, (ListPacket.truncate K ((roles u).sort (· ≤ ·))).val = (roles u).sort (· ≤ ·) :=
    fun u => ListPacket.truncate_eq K _ (by rw [Finset.length_sort]; exact hK u)
  change ((G.neighborFinset v).attach.filter (fun u => r ∈
      (ListPacket.truncate K ((roles u.val).sort (· ≤ ·))).val)).image Subtype.val = _
  simp only [hl]
  ext u
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
    Finset.mem_sort, Finset.mem_inter, mem_vertices]
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨he ▸ w.property, he ▸ hw⟩
  · rintro ⟨hu, hr⟩
    exact ⟨⟨u, hu⟩, hr, rfl⟩

theorem neighbors_inside {b : ℕ} (C : BitCode R b) (K : ℕ) (roles : V → Finset R)
    (hK : ∀ v, (roles v).card ≤ K) (v : V) (r : R) (hr : r ∈ roles v) :
    (learned G C K roles v).neighbors r = (MaskedTaskGraph.graph G (vertices roles r)).neighborFinset v := by
  rw [neighbor_filter G C K roles hK v r, MaskedTaskGraph.neighbor_inside G _ v ((mem_vertices roles r v).mpr hr)]

theorem rounds {b : ℕ} (C : BitCode R b) (K : ℕ) : (program (V := V) C K).rounds = 1 := rfl

theorem maxBits {b : ℕ} (C : BitCode R b) (K : ℕ) : (program (V := V) C K).maxBits = K * (b + 1) := rfl
end Paper.SparseRolePrepare
