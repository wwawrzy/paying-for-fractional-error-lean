import Paper.Solver.LocalSearch.GeneralCoveringOwnerSimulation
import Paper.Solver.LocalSearch.GeneralCoveringOwnerGraphCount
import Paper.Preliminaries.HighDegreeCut

/-! Count actual private high-owner bits from physical minor density.
The owner graph is the accepted gated arbitrary-C graph. HighDegreeCut is
used only after deriving its density from OwnerGraphCount. Physical flag
sets below describe outputs in the analysis; they are not global runtime
inputs. No center-self covering or partner execution is asserted here. -/
namespace Paper.GeneralCoveringOwnerHighCount
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringTaskGeometry.graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def physicalHigh (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) : Finset V :=
  (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).image Subtype.val

/-- Analysis of real per-node output bits, not a distributed enumeration step. -/
def flagged (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) : Finset V :=
  Finset.univ.filter (fun v => (E v).high = true)

theorem mem_flagged (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (v : V) :
    v ∈ flagged E ↔ (E v).high = true := by simp [flagged]

theorem mem_physicalHigh (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (v : V) :
    v ∈ physicalHigh G C D R L Δ ↔ ∃ i : D, i.val = v ∧ Δ < (ownerGraph G C D R L).degree i := by
  simp only [physicalHigh, Finset.mem_image, GeneralCoveringOwnerVirtualPrepare.mem_high]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, he, hi⟩
  · rintro ⟨i, he, hi⟩
    exact ⟨i, hi, he⟩

theorem physicalHigh_subtype_image (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    physicalHigh G C D R L Δ = (Finset.univ : Finset ↥(GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).image
      (fun i => i.val.val) := by
  ext v
  simp only [physicalHigh, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, he⟩
  · rintro ⟨i, he⟩
    exact ⟨i.val, i.property, he⟩

theorem physicalHigh_card (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    (physicalHigh G C D R L Δ).card = (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem physicalHigh_subset (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    physicalHigh G C D R L Δ ⊆ D := by
  intro v hv
  obtain ⟨i, he, _⟩ := (mem_physicalHigh G C D R L Δ v).mp hv
  exact he ▸ i.property

theorem physicalHigh_empty (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (he : GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ = ∅) : physicalHigh G C D R L Δ = ∅ := by
  simp only [physicalHigh, he, Finset.image_empty]

theorem physicalHigh_empty_centers (C : V → Finset V) (R : Finset V) (L Δ : ℕ) :
    physicalHigh G C ∅ R L Δ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact Finset.notMem_empty v (physicalHigh_subset G C ∅ R L Δ hv)

theorem owner_density (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a) :
    ((ownerGraph G C D R L).edgeFinset.card : ℝ) ≤ a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card := by
  have hh := GeneralCoveringOwnerGraphCount.count G C D R L hL (ownerGraph G C D R L)
    (Subtype.val : D → V) Subtype.val_injective (fun i => i.property) (fun _ _ h => h) hlocal hden ha
  simpa only [Fintype.card_coe] using hh

/-- Extensional bridge avoids copying the generic module's predicate decisions. -/
theorem high_eq_cut (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ = HighDegreeCut.high (ownerGraph G C D R L) Δ := by
  ext i
  rw [GeneralCoveringOwnerVirtualPrepare.mem_high]
  simp only [HighDegreeCut.high, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Product bound includes Delta=0 and empty center/high sets. -/
theorem count (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a) :
    (Δ : ℝ) * (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).card ≤
      2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card := by
  have hd : ((ownerGraph G C D R L).edgeFinset.card : ℝ) ≤
      (a * ((L + 1 : ℕ) : ℝ) ^ 4) * (Fintype.card ↥D : ℝ) := by
    simpa only [Fintype.card_coe] using owner_density G C D R L hL hlocal ha hden
  have hh := HighDegreeCut.count (ownerGraph G C D R L) Δ
    (a := a * ((L + 1 : ℕ) : ℝ) ^ 4) hd
  rw [← high_eq_cut G C D R L Δ, Fintype.card_coe] at hh
  simpa only [mul_assoc] using hh

theorem count_div (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L) (hΔ : 0 < Δ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a) :
    ((GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).card : ℝ) ≤
      (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card) / Δ := by
  have hp : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (Δ : ℝ) * (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).card := mul_comm _ _
    _ ≤ _ := count G C D R L Δ hL hlocal ha hden

theorem count_zero (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a) :
    (0 : ℝ) ≤ 2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card := by
  simpa only [Nat.cast_zero, zero_mul] using count G C D R L 0 hL hlocal ha hden

theorem admissible (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hD : D ⊆ CoveringSupport.admissible C R) : physicalHigh G C D R L Δ ⊆ CoveringSupport.admissible C R :=
  (physicalHigh_subset G C D R L Δ).trans hD

/-- Honest center-only cost bound; no claim that a selected center C-covers itself. -/
theorem cost (C : V → Finset V) (D R : Finset V) (L Δ B : ℕ) (c : V → ℝ)
    (hD : D ⊆ CoveringSupport.admissible C R)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B) :
    0 ≤ (∑ v ∈ physicalHigh G C D R L Δ, c v) ∧
    (∑ v ∈ physicalHigh G C D R L Δ, c v) ≤ (B : ℝ) * (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ).card := by
  refine ⟨Finset.sum_nonneg (fun v hv => (hc v (admissible G C D R L Δ hD hv)).1), ?_⟩
  calc
    _ ≤ ∑ _v ∈ physicalHigh G C D R L Δ, (B : ℝ) :=
      Finset.sum_le_sum (fun v hv => (hc v (admissible G C D R L Δ hD hv)).2)
    _ = _ := by simp [physicalHigh_card, mul_comm]

theorem cost_div (C : V → Finset V) (D R : Finset V) (L Δ B : ℕ) (hL : 1 ≤ L) (hΔ : 0 < Δ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (c : V → ℝ) (hD : D ⊆ CoveringSupport.admissible C R)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B) :
    (∑ v ∈ physicalHigh G C D R L Δ, c v) ≤
      (B : ℝ) * ((2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card) / Δ) :=
  (cost G C D R L Δ B c hD hc).2.trans
    (mul_le_mul_of_nonneg_left (count_div G C D R L Δ hL hΔ hlocal ha hden) (Nat.cast_nonneg B))

/-- Actual encoded learned high bits select exactly the physical image of
high owner subtypes; noncenters contribute no flags. -/
theorem learned_flags {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    flagged (GeneralCoveringOwnerSimulation.learned G ids L Δ input) = physicalHigh G C D R L Δ := by
  have hs := GeneralCoveringOwnerVirtualPrepare.private_correct G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets
  have hh (i : D) : (GeneralCoveringOwnerSimulation.learned G ids L Δ input i.val).high =
      decide (Δ < (ownerGraph G C D R L).degree i) := hs.2.1 i
  have hn (v : V) (hv : v ∉ D) : (GeneralCoveringOwnerSimulation.learned G ids L Δ input v).high = false :=
    hs.2.2.2.2.2.1 v hv
  ext v
  rw [mem_flagged, mem_physicalHigh]
  constructor
  · intro hf
    have hvD : v ∈ D := by
      by_contra hnot
      have he : (false : Bool) = true := (hn v hnot).symm.trans hf
      cases he
    let i : D := ⟨v, hvD⟩
    exact ⟨i, rfl, of_decide_eq_true ((hh i).symm.trans hf)⟩
  · rintro ⟨i, he, hdeg⟩
    subst v
    exact (hh i).trans (decide_eq_true hdeg)

theorem execute_flags {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) {In Out : Type} (P : Program V In Out) (s : V → In) :
    flagged (fun v => ((GeneralCoveringOwnerSimulation.execute ids L Δ P).runEncoded G
      (fun u => (input u, s u)) v).2) = physicalHigh G C D R L Δ := by
  have he : (fun v => ((GeneralCoveringOwnerSimulation.execute ids L Δ P).runEncoded G
      (fun u => (input u, s u)) v).2) = GeneralCoveringOwnerSimulation.learned G ids L Δ input :=
    funext (fun v => GeneralCoveringOwnerSimulation.execute_env G ids L Δ P input s v)
  rw [he]
  exact learned_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets

theorem prepared_degree {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    ∀ v, (GeneralCoveringOwnerSimulation.learned G ids L Δ input v).neighbors.card ≤ Δ := by
  intro v
  have hn := (GeneralCoveringOwnerSimulation.learned_spec G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets).2.2.2 v
  rw [hn]
  exact GeneralCoveringOwnerVirtualPrepare.public_degree_bound G C D R L Δ v

theorem learned_count {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hL : 1 ≤ L) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    (Δ : ℝ) * (flagged (GeneralCoveringOwnerSimulation.learned G ids L Δ input)).card ≤
      2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card := by
  rw [learned_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets, physicalHigh_card]
  exact count G C D R L Δ hL hlocal ha hden

theorem execute_count {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hL : 1 ≤ L) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) {In Out : Type} (P : Program V In Out) (s : V → In) :
    (Δ : ℝ) * (flagged (fun v => ((GeneralCoveringOwnerSimulation.execute ids L Δ P).runEncoded G
      (fun u => (input u, s u)) v).2)).card ≤ 2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card := by
  rw [execute_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets P s, physicalHigh_card]
  exact count G C D R L Δ hL hlocal ha hden

theorem execute_count_div {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hL : 1 ≤ L) (hΔ : 0 < Δ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) {In Out : Type} (P : Program V In Out) (s : V → In) :
    ((flagged (fun v => ((GeneralCoveringOwnerSimulation.execute ids L Δ P).runEncoded G
      (fun u => (input u, s u)) v).2)).card : ℝ) ≤ (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card) / Δ := by
  rw [execute_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets P s, physicalHigh_card]
  exact count_div G C D R L Δ hL hΔ hlocal ha hden

/-- Cost/admissibility of actual high-center bits, with the required center
admissibility and nonnegative bounded costs EXPLICIT. No repair/cover claim. -/
theorem execute_cost {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ B : ℕ)
    (hL : 1 ≤ L) (hΔ : 0 < Δ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v)
    (hDad : D ⊆ CoveringSupport.admissible C R) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B)
    {In Out : Type} (P : Program V In Out) (s : V → In) :
    let out := (GeneralCoveringOwnerSimulation.execute ids L Δ P).runEncoded G (fun u => (input u, s u))
    flagged (fun v => (out v).2) ⊆ CoveringSupport.admissible C R ∧
    (∑ v ∈ flagged (fun v => (out v).2), c v) ≤
      (B : ℝ) * ((2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card) / Δ) ∧
    (∀ v, (out v).2.metadata.owned.input = input v) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [execute_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets P s]
    exact admissible G C D R L Δ hDad
  · rw [execute_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets P s]
    exact cost_div G C D R L Δ B hL hΔ hlocal ha hden c hDad hc
  · exact GeneralCoveringOwnerSimulation.execute_private_input_retained G ids L Δ P input s

end Paper.GeneralCoveringOwnerHighCount

#print axioms Paper.GeneralCoveringOwnerHighCount.mem_flagged
#print axioms Paper.GeneralCoveringOwnerHighCount.mem_physicalHigh
#print axioms Paper.GeneralCoveringOwnerHighCount.physicalHigh_subtype_image
#print axioms Paper.GeneralCoveringOwnerHighCount.physicalHigh_card
#print axioms Paper.GeneralCoveringOwnerHighCount.physicalHigh_subset
#print axioms Paper.GeneralCoveringOwnerHighCount.physicalHigh_empty
#print axioms Paper.GeneralCoveringOwnerHighCount.physicalHigh_empty_centers
#print axioms Paper.GeneralCoveringOwnerHighCount.owner_density
#print axioms Paper.GeneralCoveringOwnerHighCount.high_eq_cut
#print axioms Paper.GeneralCoveringOwnerHighCount.count
#print axioms Paper.GeneralCoveringOwnerHighCount.count_div
#print axioms Paper.GeneralCoveringOwnerHighCount.count_zero
#print axioms Paper.GeneralCoveringOwnerHighCount.admissible
#print axioms Paper.GeneralCoveringOwnerHighCount.cost
#print axioms Paper.GeneralCoveringOwnerHighCount.cost_div
#print axioms Paper.GeneralCoveringOwnerHighCount.learned_flags
#print axioms Paper.GeneralCoveringOwnerHighCount.execute_flags
#print axioms Paper.GeneralCoveringOwnerHighCount.prepared_degree
#print axioms Paper.GeneralCoveringOwnerHighCount.learned_count
#print axioms Paper.GeneralCoveringOwnerHighCount.execute_count
#print axioms Paper.GeneralCoveringOwnerHighCount.execute_count_div
#print axioms Paper.GeneralCoveringOwnerHighCount.execute_cost
