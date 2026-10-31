import Paper.Owners.Construction.OwnerPayloadLocalKeys
import Paper.Owners.Construction.OwnerNeighborReports

/-! The last routing hop's actual capacity bound. A remaining demand owned
by a degree≤Δ root sees payload keys only from that root and its neighbors. -/
namespace Paper.OwnerPayloadSize
open BroadcastModel SevenFoundation
variable {V A : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance virtualAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

theorem owned_iff (D R : Finset V) (L : ℕ) (i r : V) :
    r ∈ OwnerNeighborReports.owned G D R L i ↔
      r ∈ closed G i ∧ r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r = i := by
  unfold OwnerNeighborReports.owned
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

theorem report_mem (D R : Finset V) (L : ℕ) (r j : V) :
    j ∈ OwnerNeighborReports.report G D R L r ↔ j ≠ OwnerSupport.owner G D r ∧
      ∃ v ∈ closed G r, j ∈ OwnerInteraction.actualSupport G D R L v := by
  unfold OwnerNeighborReports.report
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  simp only [Finset.mem_erase, Finset.mem_biUnion]

theorem owner_star (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (r : V)
    (hr : r ∈ OwnerInteraction.remaining G D R L) : r ∈ closed G (OwnerSupport.owner G D r) := by
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  have hrR : r ∈ R := by
    rw [OwnerInteraction.remaining, hinst] at hr
    exact (Finset.mem_sdiff.mp hr).1
  have hh := @OwnerSupport.owner_of_covered V _ _ G _ D r
  rw [hinst] at hh
  exact (mem_closed G r _).mpr ((hh (hcover hrR)).2.elim (fun he => Or.inl he.symm) Or.inr)

theorem owned_self (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (r : V)
    (hr : r ∈ OwnerInteraction.remaining G D R L) :
    r ∈ OwnerNeighborReports.owned G D R L (OwnerSupport.owner G D r) :=
  (owned_iff G D R L _ r).mpr ⟨owner_star G D R hcover L r hr, hr, rfl⟩

theorem report_subset (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (r : V)
    (hr : r ∈ OwnerInteraction.remaining G D R L) :
    OwnerNeighborReports.report G D R L r ⊆ OwnerNeighborReports.neighbors G D R L (OwnerSupport.owner G D r) := by
  have hh := OwnerNeighborReports.rootUnion_eq G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hh
  intro j hj
  rw [← hh hcover L (OwnerSupport.owner G D r)]
  rw [OwnerNeighborReports.rootUnion, hinst]
  exact Finset.mem_biUnion.mpr ⟨r, owned_self G D R hcover L r hr, hj⟩

theorem closed_support_subset (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (r : V)
    (hr : r ∈ OwnerInteraction.remaining G D R L) :
    (closed G r).biUnion (OwnerInteraction.actualSupport G D R L) ⊆
      insert (OwnerSupport.owner G D r) (OwnerNeighborReports.neighbors G D R L (OwnerSupport.owner G D r)) := by
  intro j hj
  by_cases he : j = OwnerSupport.owner G D r
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert_of_mem
    apply report_subset G D R hcover L r hr
    exact (report_mem G D R L r j).mpr ⟨he, Finset.mem_biUnion.mp hj⟩

theorem neighbors_card (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    (OwnerNeighborReports.neighbors G D R L i.val).card = (OwnerInteraction.graph G D R L).degree i := by
  have h1 := OwnerNeighborReports.rootUnion_eq G D R
  have h2 := OwnerNeighborReports.card_rootUnion G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at h1 h2
  rw [← h1 hcover L i.val]
  exact h2 hcover L i

theorem demand_bound {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) (active : Finset V) (f : V → A) (i : D)
    (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ) (r : V)
    (hr : r ∈ OwnerInteraction.remaining G D R L) (ho : OwnerSupport.owner G D r = i.val) :
    (TaggedDictionary.keys (OwnerPayloadRoute.demand G C P L (OwnerPayloadInputs.expected G D R L active f) r)).card ≤ Δ + 1 := by
  rw [OwnerPayloadLocalKeys.demand_keys G C P D R hcover L active f r]
  have hsub : (closed G r).biUnion (fun v => OwnerInteraction.actualSupport G D R L v ∩ active) ⊆
      insert i.val (OwnerNeighborReports.neighbors G D R L i.val) := by
    intro j hj
    obtain ⟨v, hv, hj⟩ := Finset.mem_biUnion.mp hj
    have hfull := closed_support_subset G D R hcover L r hr
      (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hj).1⟩)
    simpa only [ho] using hfull
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_insert_le i.val (OwnerNeighborReports.neighbors G D R L i.val)
  rw [neighbors_card G D R hcover L i] at hi
  omega
end Paper.OwnerPayloadSize
