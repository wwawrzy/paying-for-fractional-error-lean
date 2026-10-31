import Paper.Preliminaries.CapacitatedHall
import Paper.Preliminaries.ParentForest

/-! A single genuine rooted witness forest for simultaneous capacitated
requirements, before specializing the eligibility counts to all passes. -/
namespace Paper.WitnessForest
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

noncomputable def chosenParent (par : J → V) {k : J → ℕ} (f : (Σ r, Fin (k r)) → V) (u : V) : Option V :=
  if h : ∃ z, f z = u then some (par h.choose.fst) else none

theorem parent_at (par : J → V) {k : J → ℕ} (f : (Σ r, Fin (k r)) → V)
    (hinj : Function.Injective f) (z : Σ r, Fin (k r)) : chosenParent par f (f z) = some (par z.fst) := by
  classical
  have h : ∃ w, f w = f z := ⟨z, rfl⟩
  rw [chosenParent, dif_pos h]
  rw [hinj h.choose_spec]

theorem parent_decreases (N : J → Finset V) (par : J → V) (rank : V → ℕ)
    {k : J → ℕ} (f : (Σ r, Fin (k r)) → V) (hf : ∀ z, f z ∈ N z.fst)
    (horder : ∀ r v, v ∈ N r → rank (par r) < rank v) :
    ∀ u v, chosenParent par f u = some v → rank v < rank u := by
  classical
  intro u v huv
  by_cases h : ∃ z, f z = u
  · rw [chosenParent, dif_pos h] at huv
    have hv := Option.some.inj huv
    have hlt := horder h.choose.fst (f h.choose) (hf h.choose)
    simpa only [hv, h.choose_spec] using hlt
  · simp only [chosenParent, dif_neg h] at huv
    contradiction

theorem parent_adj (G : SimpleGraph V) (N : J → Finset V) (par : J → V)
    {k : J → ℕ} (f : (Σ r, Fin (k r)) → V) (hf : ∀ z, f z ∈ N z.fst)
    (hedge : ∀ r v, v ∈ N r → G.Adj (par r) v) :
    ∀ u v, chosenParent par f u = some v → G.Adj v u := by
  classical
  intro u v huv
  by_cases h : ∃ z, f z = u
  · rw [chosenParent, dif_pos h] at huv
    have hv := Option.some.inj huv
    have ha := hedge h.choose.fst (f h.choose) (hf h.choose)
    simpa only [hv, h.choose_spec] using ha
  · simp only [chosenParent, dif_neg h] at huv
    contradiction

structure Model (G : SimpleGraph V) (N : J → Finset V) (k : J → ℕ) (par : J → V) (rank : V → ℕ) where
  parent : V → Option V
  decrease : ∀ u v, parent u = some v → rank v < rank u
  subgraph : ParentForest.graph parent rank decrease ≤ G
  child : (Σ r, Fin (k r)) → V
  child_injective : Function.Injective child
  child_eligible : ∀ z, child z ∈ N z.fst
  parent_child : ∀ z, parent (child z) = some (par z.fst)

def Model.graph {G : SimpleGraph V} {N : J → Finset V} {k : J → ℕ} {par : J → V} {rank : V → ℕ}
    (M : Model G N k par rank) : SimpleGraph V := ParentForest.graph M.parent rank M.decrease

theorem Model.isAcyclic {G : SimpleGraph V} {N : J → Finset V} {k : J → ℕ}
    {par : J → V} {rank : V → ℕ} (M : Model G N k par rank) : M.graph.IsAcyclic :=
  ParentForest.isAcyclic M.parent rank M.decrease

theorem Model.requirement_card {G : SimpleGraph V} {N : J → Finset V} {k : J → ℕ}
    {par : J → V} {rank : V → ℕ} (M : Model G N k par rank) (r : J) :
    k r ≤ ((N r).filter (fun u => M.parent u = some (par r))).card := by
  classical
  have h := Finset.card_le_card_of_injOn (fun i : Fin (k r) => M.child ⟨r, i⟩)
    (s := Finset.univ) (t := (N r).filter (fun u => M.parent u = some (par r)))
    (fun i _ => Finset.mem_filter.mpr ⟨M.child_eligible ⟨r, i⟩, M.parent_child ⟨r, i⟩⟩)
    (fun i _ j _ hij => Fin.ext (congrArg (fun z : Σ r, Fin (k r) => z.2.val)
      (M.child_injective hij)))
  simpa using h

/-- The same forest supplies every requirement, and no child is assigned twice. -/
theorem exists_model (G : SimpleGraph V) (N : J → Finset V) (k : J → ℕ) (par : J → V) (rank : V → ℕ)
    (L : ℕ) (hL : 1 ≤ L) (hrow : ∀ r, L * k r ≤ (N r).card)
    (hcol : ∀ v, (Finset.univ.filter (fun r => v ∈ N r)).card ≤ L)
    (horder : ∀ r v, v ∈ N r → rank (par r) < rank v)
    (hedge : ∀ r v, v ∈ N r → G.Adj (par r) v) : Nonempty (Model G N k par rank) := by
  classical
  obtain ⟨f, hinj, hf⟩ := CapacitatedHall.exists_assignment N k L hL hrow hcol
  refine ⟨{
    parent := chosenParent par f
    decrease := parent_decreases N par rank f hf horder
    subgraph := ?_
    child := f
    child_injective := hinj
    child_eligible := hf
    parent_child := parent_at par f hinj }⟩
  intro u v huv
  rcases huv with hu | hv
  · exact (parent_adj G N par f hf hedge u v hu).symm
  · exact parent_adj G N par f hf hedge v u hv
end Paper.WitnessForest
