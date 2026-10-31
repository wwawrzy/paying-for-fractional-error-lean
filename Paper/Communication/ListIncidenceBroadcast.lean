import Paper.Preliminaries.ListPacket
import Paper.Preliminaries.IncidentHierarchy
import Paper.Preliminaries.SevenFoundation
import Mathlib.Data.Finset.Sort

/-! One genuine bounded broadcast distributes all original lists incident
with each candidate. Degree and the private received family may be large;
every sender sends just one list of at most f identifiers. -/
namespace Paper.ListIncidenceBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def packet (f : ℕ) (s : Finset V) := ListPacket.truncate f (s.sort (· ≤ ·))

theorem packet_set (f : ℕ) (s : Finset V) (hs : s.card ≤ f) : (packet f s).val.toFinset = s := by
  rw [packet, ListPacket.truncate_eq f _ (by simpa only [Finset.length_sort] using hs)]
  exact Finset.sort_toFinset s (· ≤ ·)

def received (v : V) (N : Finset V) (own : Finset V)
    (msg : N → {l : List V // l.length ≤ f}) : Finset (Finset V) :=
  (insert own (N.attach.image (fun u => (msg u).val.toFinset))).filter (fun s => v ∈ s)

def round (f : ℕ) : Round V (Finset V) (Finset (Finset V)) {l : List V // l.length ≤ f} where
  send _ _ s := packet f s
  update v N s msg := received v N s msg

def program {b : ℕ} (C : BitCode V b) (f : ℕ) :=
  Program.broadcast (f * (b + 1)) (ListPacket.bounded C f) (round f)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def family (lists : V → Finset V) : Finset (Finset V) := (Finset.univ.image lists).erase ∅

theorem mem_family (lists : V → Finset V) (t : Finset V) :
    t ∈ family lists ↔ t ≠ ∅ ∧ ∃ u, lists u = t := by
  simp only [family, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]

theorem correct {b : ℕ} (C : BitCode V b) (f : ℕ) (lists : V → Finset V)
    (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ closed G u) (v : V) :
    (program C f).run G lists v = IncidentHierarchy.incident (family lists) v := by
  change received v (G.neighborFinset v) (lists v)
    (fun u => packet f (lists u.val)) = _
  ext t
  simp only [received, IncidentHierarchy.incident, Finset.mem_filter, Finset.mem_insert, Finset.mem_image,
    Finset.mem_attach, true_and, packet_set f _ (hbound _)]
  constructor
  · rintro ⟨he | ⟨u, he⟩, hv⟩
    · refine ⟨(mem_family lists t).mpr ⟨?_, v, he.symm⟩, hv⟩
      intro ht
      simpa only [ht, Finset.notMem_empty] using hv
    · refine ⟨(mem_family lists t).mpr ⟨?_, u.val, he⟩, hv⟩
      intro ht
      simpa only [ht, Finset.notMem_empty] using hv
  · rintro ⟨ht, hv⟩
    obtain ⟨_, u, rfl⟩ := (mem_family lists t).mp ht
    have hu : u ∈ closed G v := (closed_symm G u v).mpr (hlocal u hv)
    rcases (mem_closed G u v).mp hu with he | hadj
    · subst u
      exact ⟨Or.inl rfl, hv⟩
    · exact ⟨Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr hadj⟩, rfl⟩, hv⟩

theorem rounds {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).rounds = 1 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (f : ℕ) : (program C f).maxBits = f * (b + 1) := rfl
end Paper.ListIncidenceBroadcast
