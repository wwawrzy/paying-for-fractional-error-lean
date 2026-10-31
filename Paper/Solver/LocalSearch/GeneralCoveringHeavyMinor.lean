import Paper.Solver.LocalSearch.GeneralCoveringOwnerSupport
import Paper.Preliminaries.StarMap

/-! Retain marked P and all centers D for the actual optional C-owner.
An unmarked some-owner contracts to that owner; none stays fixed solely
as a contraction identity. This does not assign it an owner. The physical
star model and support-neighbor witnesses precede degree/heavy counting. -/
namespace Paper.GeneralCoveringHeavyMinor
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def contract (C : V → Finset V) (D R P : Finset V) (u : V) : V :=
  if u ∈ P then u else
    match GeneralCoveringOwners.owner C D R u with
    | none => u
    | some d => d

theorem contract_none (C : V → Finset V) (D R P : Finset V) {u : V}
    (ho : GeneralCoveringOwners.owner C D R u = none) : contract C D R P u = u := by
  by_cases hp : u ∈ P <;> simp [contract, hp, ho]

theorem fixed (C : V → Finset V) (D R P : Finset V) {u : V}
    (hu : u ∈ D ∪ P) : contract C D R P u = u := by
  by_cases hp : u ∈ P
  · simp [contract, hp]
  · have hd : u ∈ D := (Finset.mem_union.mp hu).resolve_right hp
    simp only [contract, if_neg hp, GeneralCoveringOwners.owner_center C D R hd]

theorem star (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (u : V) :
    contract C D R P u = u ∨ G.Adj (contract C D R P u) u := by
  by_cases hp : u ∈ P
  · exact Or.inl (by simp [contract, hp])
  · cases ho : GeneralCoveringOwners.owner C D R u with
    | none => exact Or.inl (contract_none C D R P ho)
    | some d =>
      simpa only [contract, if_neg hp, ho] using
        GeneralCoveringOwners.owner_star G C D R hlocal ho

def graph (C : V → Finset V) (D R P : Finset V) : SimpleGraph ↥(D ∪ P) :=
  StarMap.graph G (contract C D R P) (D ∪ P)

noncomputable def model (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) : DepthOne.StarModel (graph G C D R P) G :=
  StarMap.model G _ _ (fun _ hu => fixed C D R P hu) (star G C D R P hlocal)

theorem isMinor (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    SimpleGraph.IsMinor (graph G C D R P) G := ⟨(model G C D R P hlocal).toMinorModel⟩

theorem contract_owned (C : V → Finset V) (D R P : Finset V) {u d : V}
    (ho : GeneralCoveringOwners.owner C D R u = some d) :
    contract C D R P u ∈ R ∪ D ∧
      GeneralCoveringOwners.owner C D R (contract C D R P u) = some d := by
  by_cases hp : u ∈ P
  · simpa only [contract, if_pos hp] using
      (And.intro (GeneralCoveringOwners.owner_domain C D R ho) ho)
  · have hd : d ∈ D := GeneralCoveringOwners.owner_mem C D R ho
    simpa only [contract, if_neg hp, ho] using
      (And.intro (Finset.mem_union_right R hd) (GeneralCoveringOwners.owner_center C D R hd))

theorem contract_retained (C : V → Finset V) (D R P : Finset V) {u d : V}
    (ho : GeneralCoveringOwners.owner C D R u = some d) : contract C D R P u ∈ D ∪ P := by
  by_cases hp : u ∈ P
  · simpa only [contract, if_pos hp] using Finset.mem_union_right D hp
  · simpa only [contract, if_neg hp, ho] using
      Finset.mem_union_left P (GeneralCoveringOwners.owner_mem C D R ho)

/-- The contraction preserves optional labels, including none. It does
not assert that an unowned fixed vertex lies among retained centers. -/
theorem contract_owner (C : V → Finset V) (D R P : Finset V) (u : V) :
    GeneralCoveringOwners.owner C D R (contract C D R P u) =
      GeneralCoveringOwners.owner C D R u := by
  cases ho : GeneralCoveringOwners.owner C D R u with
  | none => simpa only [contract_none C D R P ho] using ho
  | some d => exact (contract_owned C D R P ho).2

/-- Every actual S0 label supplies a distinct retained neighbor, except
that a center's own label is excluded. A noncenter's own label is kept. -/
theorem support_neighbor (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v d : V}
    (hv : v ∈ P) (hd : d ∈ GeneralCoveringOwnerSupport.support G C D R v)
    (hneq : v ∈ D → d ≠ v) :
    ∃ y : ↥(D ∪ P), (graph G C D R P).Adj ⟨v, Finset.mem_union_right D hv⟩ y ∧
      GeneralCoveringOwners.owner C D R y.val = some d := by
  have hfixv := fixed C D R P (Finset.mem_union_right D hv)
  by_cases hself : GeneralCoveringOwners.owner C D R v = some d
  · have hvD : v ∉ D := by
      intro hvD
      have he : d = v := Option.some.inj
        (hself.symm.trans (GeneralCoveringOwners.owner_center C D R hvD))
      exact hneq hvD he
    have hdD := GeneralCoveringOwners.owner_mem C D R hself
    have hne : d ≠ v := fun he => hvD (he ▸ hdD)
    have ha : G.Adj v d :=
      ((GeneralCoveringOwners.owner_star G C D R hlocal hself).resolve_left hne).symm
    refine ⟨⟨d, Finset.mem_union_left P hdD⟩, ?_, GeneralCoveringOwners.owner_center C D R hdD⟩
    exact ⟨fun he => hne (congrArg Subtype.val he).symm, v, d,
      hfixv, fixed C D R P (Finset.mem_union_left P hdD), ha⟩
  · obtain ⟨u, hu, hud⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v d).mp hd
    let y := contract C D R P u
    have hy := contract_retained C D R P hud
    have hylab : GeneralCoveringOwners.owner C D R y = some d := (contract_owned C D R P hud).2
    have hyne : y ≠ v := by
      intro he
      exact hself (he ▸ hylab)
    have huv : G.Adj v u := by
      rcases (mem_closed G u v).mp hu with he | ha
      · exact False.elim (hself (he ▸ hud))
      · exact ha
    refine ⟨⟨y, hy⟩, ?_, hylab⟩
    exact ⟨fun he => hyne (congrArg Subtype.val he).symm, v, u, hfixv, rfl, huv⟩

end Paper.GeneralCoveringHeavyMinor

#print axioms Paper.GeneralCoveringHeavyMinor.contract_none
#print axioms Paper.GeneralCoveringHeavyMinor.fixed
#print axioms Paper.GeneralCoveringHeavyMinor.star
#print axioms Paper.GeneralCoveringHeavyMinor.model
#print axioms Paper.GeneralCoveringHeavyMinor.isMinor
#print axioms Paper.GeneralCoveringHeavyMinor.contract_owned
#print axioms Paper.GeneralCoveringHeavyMinor.contract_retained
#print axioms Paper.GeneralCoveringHeavyMinor.contract_owner
#print axioms Paper.GeneralCoveringHeavyMinor.support_neighbor
