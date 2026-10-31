import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairObserver
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRootFrames

/-! Every boundary source queried by the actual repair observer already has
a packet in the actual root-frame output. Partners are recomputed by their
literal center-bit broadcast from the retained original metadata. -/
namespace Paper.GeneralCoveringOwnerRepairFrames
open BroadcastModel SevenFoundation
open GeneralCoveringOwnerRepairObserver
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C targets : V → Finset V) (D R : Finset V) (L Δ r : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u)
variable (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D))
variable (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v)
variable (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets

local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q

def environments {b : ℕ} (ids : BitCode V b) : V → GeneralCoveringOwnerVirtualPrepare.Env V :=
  fun v => ((GeneralCoveringOwnerRootFrames.program ids L Δ r).runEncoded G input v).env

omit hinc hlocal hD hR hC hTargets in
theorem environments_eq {b : ℕ} (ids : BitCode V b) :
    environments G L Δ r input ids = GeneralCoveringOwnerSimulation.learned G ids L Δ input := by
  funext v
  exact GeneralCoveringOwnerRootFrames.env_retained G ids L Δ r input v

theorem partner_eq {b : ℕ} (ids : BitCode V b) (v : V) :
    (states G (environments G L Δ r input ids) v).partner =
      GeneralCoveringPartners.partner G C D R L v := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets
  unfold states
  rw [environments_eq G L Δ r input ids]
  have hm : (fun u => (GeneralCoveringOwnerSimulation.learned G ids L Δ input u).metadata) =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input := funext hs.1
  rw [hm, GeneralCoveringPartners.attach_correct G C D R L _ hD (fun _ => rfl) hC hlocal]

theorem low_eq {b : ℕ} (ids : BitCode V b) (v : V) :
    low (states G (environments G L Δ r input ids) v) = decide (v ∈ U) := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets
  unfold low states
  rw [environments_eq G L Δ r input ids, hs.2.2.1 v, hs.2.1 v, hD v]
  by_cases hu : v ∈ U
  · obtain ⟨i, he, _⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q v).mp hu
    have hd : v ∈ D := he ▸ i.property
    simp only [decide_eq_true hu, decide_eq_true hd, Bool.and_self]
  · simp only [decide_eq_false hu, Bool.false_and]

/-- All own and neighboring boundary roots are in the packets actually
delivered by the original-C routing protocol, with no physical-ball bound. -/
theorem roots_subset {b : ℕ} (ids : BitCode V b) (v : V) :
    ((core ids).runEncoded G (environments G L Δ r input ids) v).roots ⊆
      TaggedDictionary.keys ((GeneralCoveringOwnerRootFrames.program ids L Δ r).runEncoded G input v).roots.val := by
  rw [run_core, Program.runEncoded_eq_run, run_request]
  change roots v (G.neighborFinset v) (states G (environments G L Δ r input ids) v)
      (fun u => message (states G (environments G L Δ r input ids) u.val)) ⊆ _
  rw [GeneralCoveringOwnerRootFrames.keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  intro u hu
  rcases (roots_iff _ _ _ _ _).mp hu with ⟨hl, he⟩ | ⟨w, rfl, hl, hp⟩
  · subst u
    rw [low_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v] at hl
    have hv := of_decide_eq_true hl
    obtain ⟨i, he, _⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q v).mp hv
    exact Finset.mem_inter.mpr ⟨GeneralCoveringOwnerRouteLabels.root_label G C D R L (he ▸ i.property), hv⟩
  · change low (states G (environments G L Δ r input ids) w.val) = true at hl
    change (states G (environments G L Δ r input ids) w.val).partner = some v at hp
    rw [low_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids w.val] at hl
    rw [partner_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids w.val] at hp
    have ha := GeneralCoveringPartners.light_admissible G C D R L hp
    have ho := GeneralCoveringPartners.owner_in_support G C D R L hlocal hp
    exact Finset.mem_inter.mpr
      ⟨GeneralCoveringOwnerRouteLabels.light_label G C D R L ha.1 ha.2.1 ho, of_decide_eq_true hl⟩

end Paper.GeneralCoveringOwnerRepairFrames

#print axioms Paper.GeneralCoveringOwnerRepairFrames.environments_eq
#print axioms Paper.GeneralCoveringOwnerRepairFrames.partner_eq
#print axioms Paper.GeneralCoveringOwnerRepairFrames.low_eq
#print axioms Paper.GeneralCoveringOwnerRepairFrames.roots_subset
