import Paper.Endpoints.Components.IncidenceGraph
import Paper.Averaging.Tasks.ActiveTaskContext
import Paper.Preliminaries.ShortChains
import Paper.Communication.ComponentLocality

/-! Proof-side contexts and input restrictions for parallel component search.
Component sets are correctness certificates, never inputs to the executable.
The restriction changes only active and demand bits outside the component. -/
namespace Paper.IncidenceComponent
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (I : SimpleGraph V) [DecidableRel I.Adj]

noncomputable def vertices (X : I.ConnectedComponent) : Finset V := by
  classical
  exact X.supp.toFinset

theorem mem_vertices (X : I.ConnectedComponent) (v : V) :
    v ∈ vertices I X ↔ v ∈ X.supp := by
  classical
  simp only [vertices, Set.mem_toFinset]

omit [Fintype V] [LinearOrder V] [DecidableRel I.Adj] in
theorem reachable_closed (X : I.ConnectedComponent) {u v : V}
    (hu : u ∈ X.supp) (h : I.Reachable u v) : v ∈ X.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu ⊢
  exact (SimpleGraph.ConnectedComponent.sound h).symm.trans hu

omit [Fintype V] [LinearOrder V] [DecidableRel I.Adj] in
theorem walk_stays (X : I.ConnectedComponent) {u v : V} (p : I.Walk u v) :
    u ∈ X.supp → ∀ z ∈ p.support, z ∈ X.supp := by
  induction p with
  | nil =>
    intro hu z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact hu
  | @cons u v w h p ih =>
    intro hu z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih (X.mem_supp_of_adj_mem_supp hu h) z hz

/-- A bounded component supplies the existing local-search geometry contract. -/
noncomputable def context (X : I.ConnectedComponent) (d : ℕ)
    (hdiam : ∀ u ∈ X.supp, ∀ v ∈ X.supp, ∃ p : I.Walk u v, p.length ≤ d) :
    ActiveTask.Context I := by
  classical
  refine ⟨vertices I X, ?_, d, ?_⟩
  · obtain ⟨v, hv⟩ := X.nonempty_supp
    exact ⟨v, (mem_vertices I X v).mpr hv⟩
  · intro x y
    have hx := (mem_vertices I X x.val).mp x.property
    have hy := (mem_vertices I X y.val).mp y.property
    obtain ⟨p, hp⟩ := hdiam x.val hx y.val hy
    have hs : ∀ z ∈ p.support, z ∈ vertices I X :=
      fun z hz => (mem_vertices I X z).mpr (walk_stays I X p hx z hz)
    exact ⟨p.induce (vertices I X : Set V) hs,
      (ShortChains.induce_length I (vertices I X) p hs).le.trans hp⟩

theorem context_vertices (X : I.ConnectedComponent) (d : ℕ)
    (hdiam : ∀ u ∈ X.supp, ∀ v ∈ X.supp, ∃ p : I.Walk u v, p.length ≤ d) :
    (context I X d hdiam).vertices = vertices I X := rfl

theorem context_diameter (X : I.ConnectedComponent) (d : ℕ)
    (hdiam : ∀ u ∈ X.supp, ∀ v ∈ X.supp, ∃ p : I.Walk u v, p.length ≤ d) :
    (context I X d hdiam).diameter = d := rfl

omit I [DecidableRel I.Adj] in
theorem rows_stay (C : V → Finset V) (R : Finset V)
    (X : (CoveringIncidence.graph C R).ConnectedComponent) :
    ∀ r ∈ R ∩ vertices (CoveringIncidence.graph C R) X,
      C r ⊆ vertices (CoveringIncidence.graph C R) X := by
  intro r hr v hv
  obtain ⟨hrR, hrX⟩ := Finset.mem_inter.mp hr
  apply (mem_vertices _ X v).mpr
  exact reachable_closed _ X ((mem_vertices _ X r).mp hrX)
    (CoveringIncidence.candidate_reachable C R hrR hv)

omit I [DecidableRel I.Adj] in
/-- An analysis-only input assignment, not a program constructor. -/
def restrict {B : ℕ} (H : Finset V)
    (s : V → GeneralCoveringFractional.Input V B) (v : V) :
    GeneralCoveringFractional.Input V B :=
  { s v with active := (s v).active && decide (v ∈ H),
             demand := (s v).demand && decide (v ∈ H) }

omit I [DecidableRel I.Adj] [Fintype V] in
theorem restrict_inside {B : ℕ} (H : Finset V)
    (s : V → GeneralCoveringFractional.Input V B) (v : V) (hv : v ∈ H) :
    restrict H s v = s v := by
  simp [restrict, hv]

omit I [DecidableRel I.Adj] [Fintype V] in
theorem restrict_active {B : ℕ} (H : Finset V)
    (s : V → GeneralCoveringFractional.Input V B)
    (ha : ∀ v ∈ H, (s v).active = true) (v : V) :
    (restrict H s v).active = decide (v ∈ H) := by
  by_cases hv : v ∈ H <;> simp [restrict, hv, ha]

omit I [DecidableRel I.Adj] [Fintype V] in
theorem restrict_demand {B : ℕ} (H R : Finset V)
    (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (v : V) :
    (restrict H s v).demand = decide (v ∈ R ∩ H) := by
  by_cases hr : v ∈ R <;> by_cases hv : v ∈ H <;>
    simp [restrict, hd, Finset.mem_inter, hr, hv]

/-- Every encoded program has the same output inside the component after
restricting the active and demand bits outside it. -/
theorem encoded_restriction {B : ℕ} {Out : Type}
    (P : Program V (GeneralCoveringFractional.Input V B) Out)
    (X : I.ConnectedComponent) (s : V → GeneralCoveringFractional.Input V B)
    (v : V) (hv : v ∈ X.supp) :
    P.runEncoded I s v = P.runEncoded I (restrict (vertices I X) s) v := by
  apply ComponentLocality.encoded_agreement I P X.supp
    (fun u hu w h => X.mem_supp_of_adj_mem_supp hu h) s _ ?_ v hv
  intro w hw
  exact (restrict_inside (vertices I X) s w ((mem_vertices I X w).mpr hw)).symm

end Paper.IncidenceComponent

#print axioms Paper.IncidenceComponent.context_vertices
#print axioms Paper.IncidenceComponent.context_diameter
#print axioms Paper.IncidenceComponent.rows_stay
#print axioms Paper.IncidenceComponent.restrict_active
#print axioms Paper.IncidenceComponent.restrict_demand
#print axioms Paper.IncidenceComponent.encoded_restriction
