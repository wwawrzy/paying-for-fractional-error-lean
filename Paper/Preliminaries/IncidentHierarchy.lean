import Paper.Preliminaries.ComputableCores

/-! Every vertex computes the exact incident portion of every core level
from its original incident family, with no further messages or graph input. -/
namespace Paper.IncidentHierarchy
variable {V : Type} [DecidableEq V]

def incident (H : Finset (Finset V)) (v : V) : Finset (Finset V) := H.filter (fun s => v ∈ s)

def globalLevel (H : Finset (Finset V)) (q : ℕ) : ℕ → Finset (Finset V)
  | 0 => H
  | n + 1 => ComputableCores.cores (globalLevel H q n) q

def localLevel (v : V) (H : Finset (Finset V)) (q : ℕ) : ℕ → Finset (Finset V)
  | 0 => H
  | n + 1 => incident (ComputableCores.cores (localLevel v H q n) q) v

variable [Fintype V]

theorem incident_step (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (v : V) :
    incident (ComputableCores.cores (incident H v) q) v = incident (ComputableCores.cores H q) v := by
  rw [ComputableCores.eq_cores _ q hq, ComputableCores.eq_cores _ q hq]
  ext C
  simp only [incident, Finset.mem_filter]
  exact (CoreHierarchy.incident_cores H q hq v C).symm

theorem local_global (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (v : V) (n : ℕ) :
    localLevel v (incident H v) q n = incident (globalLevel H q n) v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [localLevel, ih, incident_step _ q hq]; rfl

theorem subset_original (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (n : ℕ)
    (s : Finset V) (hs : s ∈ globalLevel H q n) : ∃ t ∈ H, s ⊆ t := by
  induction n generalizing s with
  | zero => exact ⟨s, hs, Finset.Subset.refl _⟩
  | succ n ih =>
    rw [globalLevel, ComputableCores.eq_cores _ q hq] at hs
    obtain ⟨t, ht, hst⟩ := CoreHierarchy.core_subset_original _ q hq hs
    obtain ⟨u, hu, htu⟩ := ih t ht
    exact ⟨u, hu, hst.trans htu⟩
end Paper.IncidentHierarchy
