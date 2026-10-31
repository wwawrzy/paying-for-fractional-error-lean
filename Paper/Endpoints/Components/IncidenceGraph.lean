import Paper.Solver.LocalSearch.GeneralCoveringInputNormalization

/-! The demanded covering-incidence graph and its actual local preparation.
The graph is a proof-side object. The executable reads the existing private
input and physical neighbor list, and broadcasts only the demand bit. -/
namespace Paper.CoveringIncidence
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

/-- Only demanded rows create incidence edges; self incidences create no loop. -/
def graph (C : V → Finset V) (R : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u ∈ R ∧ v ∈ C u) ∨ (v ∈ R ∧ u ∈ C v))
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance graphAdjDecidable (C : V → Finset V) (R : Finset V) :
    DecidableRel (graph C R).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u ∈ R ∧ v ∈ C u) ∨ (v ∈ R ∧ u ∈ C v))))

omit [DecidableEq V] in
theorem adj_iff (C : V → Finset V) (R : Finset V) (u v : V) :
    (graph C R).Adj u v ↔
      u ≠ v ∧ ((u ∈ R ∧ v ∈ C u) ∨ (v ∈ R ∧ u ∈ C v)) := Iff.rfl

theorem candidate_self_or_adj (C : V → Finset V) (R : Finset V)
    {r v : V} (hr : r ∈ R) (hv : v ∈ C r) :
    v = r ∨ (graph C R).Adj r v := by
  by_cases he : v = r
  · exact Or.inl he
  · exact Or.inr ⟨Ne.symm he, Or.inl ⟨hr, hv⟩⟩

/-- Each covering candidate lies in the same logical component as its demand. -/
theorem candidate_reachable (C : V → Finset V) (R : Finset V)
    {r v : V} (hr : r ∈ R) (hv : v ∈ C r) : (graph C R).Reachable r v := by
  rcases candidate_self_or_adj C R hr hv with he | ha
  · subst v; exact ⟨.nil⟩
  · exact ha.reachable

omit [DecidableEq V] in
/-- Trimming arbitrary zero-demand rows leaves the incidence graph unchanged. -/
theorem graph_trimmed [LinearOrder V] (C : V → Finset V) (R : Finset V) :
    graph (GeneralCoveringInputNormalization.trimmed C R) R = graph C R := by
  ext u v
  simp only [adj_iff, GeneralCoveringInputNormalization.mem_trimmed]
  tauto

/-- The retained list is computed from local incidence lists and received bits.
The attached neighbor identifiers are private memory, not transmitted payloads. -/
def neighbors {B : ℕ} (N : Finset V) (s : GeneralCoveringFractional.Input V B)
    (incoming : N → Bool) : Finset V :=
  (N.attach.filter (fun u =>
    (s.demand && decide (u.val ∈ s.candidates)) ||
      (incoming u && decide (u.val ∈ s.targets)))).image Subtype.val

theorem mem_neighbors {B : ℕ} (N : Finset V) (s : GeneralCoveringFractional.Input V B)
    (incoming : N → Bool) (u : V) :
    u ∈ neighbors N s incoming ↔ ∃ h : u ∈ N,
      (s.demand = true ∧ u ∈ s.candidates) ∨
        (incoming ⟨u, h⟩ = true ∧ u ∈ s.targets) := by
  simp only [neighbors, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
    true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, he⟩
    subst u
    exact ⟨w.property, hw⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

def round (B : ℕ) : Round V (GeneralCoveringFractional.Input V B)
    (Finset V × GeneralCoveringFractional.Input V B) Bool where
  send _ _ s := s.demand
  update _ N s incoming := (neighbors N s incoming, s)

/-- One demand-bit broadcast. No graph, demand set, row function, or vertex
enumeration occurs in this constructor. The complete private input is retained. -/
def program (B : ℕ) : Program V (GeneralCoveringFractional.Input V B)
    (Finset V × GeneralCoveringFractional.Input V B) :=
  .broadcast 1 BitCode.bool (round B)

theorem rounds (B : ℕ) : (program (V := V) B).rounds = 1 := rfl

theorem maxBits (B : ℕ) : (program (V := V) B).maxBits = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only locality of demanded rows is needed; unused rows can be arbitrary. -/
theorem graph_le (C : V → Finset V) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) : graph C R ≤ G := by
  intro u v h
  rcases h.2 with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · rcases (mem_closed G v u).mp (hlocal u hu hv) with he | ha
    · exact False.elim (h.1 he.symm)
    · exact ha
  · rcases (mem_closed G u v).mp (hlocal v hv hu) with he | ha
    · exact False.elim (h.1 he)
    · exact ha.symm

theorem candidate_mem_closed (C : V → Finset V) (R : Finset V)
    {r v : V} (hr : r ∈ R) (hv : v ∈ C r) :
    v ∈ closed (graph C R) r := by
  exact (mem_closed (graph C R) v r).mpr (candidate_self_or_adj C R hr hv)

theorem run_program (B : ℕ) (s : V → GeneralCoveringFractional.Input V B) (v : V) :
    (program B).runEncoded G s v =
      (neighbors (G.neighborFinset v) (s v) (fun u => (s u.val).demand), s v) := by
  rw [Program.runEncoded_eq_run]
  rfl

theorem retains_input (B : ℕ) (s : V → GeneralCoveringFractional.Input V B) (v : V) :
    ((program B).runEncoded G s v).2 = s v := by
  rw [run_program]

/-- The actual prepared list is exactly the logical incidence neighborhood.
All global row and demand data occur only in this specification. -/
theorem prepared_neighbors (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {B : ℕ} (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v)
    (ht : ∀ v, (s v).targets = targets v) (v : V) :
    ((program B).runEncoded G s v).1 = (graph C R).neighborFinset v := by
  rw [run_program]
  ext u
  simp only [mem_neighbors, hd, hC, ht, decide_eq_true_eq, hinc,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨ha, hi⟩
    exact ⟨ha.ne, hi⟩
  · intro hi
    exact ⟨graph_le G C R hlocal hi, hi.2⟩

/-- The on-wire message is exactly the existing private demand flag. -/
theorem sends_demand (B : ℕ) (v : V) (s : GeneralCoveringFractional.Input V B) :
    (round B).send v (G.neighborFinset v) s = s.demand := rfl

end Paper.CoveringIncidence

#print axioms Paper.CoveringIncidence.graph_le
#print axioms Paper.CoveringIncidence.candidate_reachable
#print axioms Paper.CoveringIncidence.graph_trimmed
#print axioms Paper.CoveringIncidence.prepared_neighbors
#print axioms Paper.CoveringIncidence.retains_input
#print axioms Paper.CoveringIncidence.rounds
#print axioms Paper.CoveringIncidence.maxBits
