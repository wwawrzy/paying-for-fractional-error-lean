import Paper.Solver.LocalSearch.GeneralCoveringOwnerDiscovery

/-! Actual original-C discovery correctness. Uncapped physical reports of
some-i representatives are exactly virtual neighbors. Finite capped-union
laws give the strict high threshold and full low lists. The final theorem
is about the literal encoded six-round private program, not a supplied
metadata state or neighborhood. Runtime and resources stay in the frozen core. -/
namespace Paper.GeneralCoveringOwnerDiscoveryCorrect
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable def supportUnion (C : V → Finset V) (D R : Finset V) (L : ℕ) (r : V) : Finset V :=
  (closed G r).biUnion (lightSupport G C D R L)

noncomputable def representatives (C : V → Finset V) (D R : Finset V) (i : V) : Finset V :=
  (closed G i).filter (fun r => GeneralCoveringOwners.owner C D R r = some i)

noncomputable def uncapped (C : V → Finset V) (D R : Finset V) (L : ℕ) (i r : V) : Finset V :=
  (supportUnion G C D R L r).erase i

noncomputable def rootUnion (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : V) : Finset V :=
  (representatives G C D R i).biUnion (uncapped G C D R L i)

noncomputable def family (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : V) : Finset (Finset V) :=
  (representatives G C D R i).image (uncapped G C D R L i)

noncomputable def neighbors (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : D) : Finset V :=
  ((ownerGraph G C D R L).neighborFinset i).image Subtype.val

noncomputable def capped (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (i : V) : Finset V :=
  PrefixSet.take (Δ + 1) (PrefixSet.union (family G C D R L i) (Δ + 1))

theorem family_union (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : V) :
    (family G C D R L i).biUnion id = rootUnion G C D R L i := by
  ext j
  simp only [family, rootUnion, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, hj⟩
    exact ⟨r, hr, hj⟩
  · rintro ⟨r, hr, hj⟩
    exact ⟨uncapped G C D R L i r, ⟨r, hr, rfl⟩, hj⟩

theorem root_neighbors (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) :
    rootUnion G C D R L i.val = neighbors G C D R L i := by
  ext j
  constructor
  · intro hj
    obtain ⟨r, hr, hjr⟩ := Finset.mem_biUnion.mp hj
    have ho := (Finset.mem_filter.mp hr).2
    obtain ⟨hne, hju⟩ := Finset.mem_erase.mp hjr
    obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hju
    have hgate := (mem_lightSupport G C D R L v j).mp hjv
    have his : i.val ∈ GeneralCoveringOwnerSupport.support G C D R v :=
      (GeneralCoveringOwnerSupport.mem_support G C D R v i.val).mpr
        ⟨r, (closed_symm G r v).mpr hv, ho⟩
    have hiv : i.val ∈ lightSupport G C D R L v :=
      (mem_lightSupport G C D R L v i.val).mpr ⟨hgate.1, hgate.2.1, his⟩
    have hjD := lightSupport_labels G C D R L v hjv
    apply Finset.mem_image.mpr
    refine ⟨⟨j, hjD⟩, ?_, rfl⟩
    apply ((ownerGraph G C D R L).mem_neighborFinset i ⟨j, hjD⟩).mpr
    exact ⟨fun he => hne (congrArg Subtype.val he).symm, v, hiv, hjv⟩
  · intro hImage
    have hImage' : j ∈ ((ownerGraph G C D R L).neighborFinset i).image (Subtype.val : D → V) := by
      simpa only [neighbors] using hImage
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hImage'
    subst j
    obtain ⟨hne, v, hiv, hqv⟩ := ((ownerGraph G C D R L).mem_neighborFinset i q).mp hq
    have his := ((mem_lightSupport G C D R L v i.val).mp hiv).2.2
    obtain ⟨r, hr, ho⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v i.val).mp his
    have hstar : r ∈ closed G i.val :=
      (mem_closed G r i.val).mpr
        ((GeneralCoveringOwners.owner_star G C D R hlocal ho).elim
          (fun he => Or.inl he.symm) Or.inr)
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hstar, ho⟩, ?_⟩
    apply Finset.mem_erase.mpr
    refine ⟨fun he => hne (Subtype.ext he.symm), ?_⟩
    exact Finset.mem_biUnion.mpr ⟨v, (closed_symm G r v).mp hr, hqv⟩

theorem family_neighbors (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) :
    (family G C D R L i.val).biUnion id = neighbors G C D R L i :=
  (family_union G C D R L i.val).trans (root_neighbors G C D R L hlocal i)

theorem card_family (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) :
    ((family G C D R L i.val).biUnion id).card = (ownerGraph G C D R L).degree i := by
  calc
    _ = (neighbors G C D R L i).card := congrArg Finset.card (family_neighbors G C D R L hlocal i)
    _ = ((ownerGraph G C D R L).neighborFinset i).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    _ = _ := rfl

theorem capped_subset (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) :
    capped G C D R L Δ i.val ⊆ neighbors G C D R L i := by
  rw [← family_neighbors G C D R L hlocal i]
  exact (PrefixSet.subset (Δ + 1) _).trans (PrefixSet.union_subset _ _)

theorem capped_high (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) :
    (Δ < (capped G C D R L Δ i.val).card) ↔ Δ < (ownerGraph G C D R L).degree i := by
  have hh := PrefixSet.capped_union_small_iff (family G C D R L i.val) (Δ + 1)
  rw [card_family G C D R L hlocal i] at hh
  change (capped G C D R L Δ i.val).card < Δ + 1 ↔ (ownerGraph G C D R L).degree i < Δ + 1 at hh
  omega

theorem capped_low (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) (hlow : (ownerGraph G C D R L).degree i ≤ Δ) :
    capped G C D R L Δ i.val = neighbors G C D R L i := by
  have hcard : ((family G C D R L i.val).biUnion id).card < Δ + 1 := by
    rw [card_family G C D R L hlocal i]
    omega
  have hs := (PrefixSet.capped_union_small_iff (family G C D R L i.val) (Δ + 1)).mpr hcard
  exact (PrefixSet.capped_union_low_eq _ _ hs).trans (family_neighbors G C D R L hlocal i)

noncomputable def metadata (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (input : V → GeneralCoveringOwners.Input V) : V → GeneralCoveringOwnerSupport.State V :=
  GeneralCoveringOwnerSupport.expected G C D R L (fun v => ⟨input v, GeneralCoveringOwners.owner C D R v⟩)

theorem metadata_outgoing (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    GeneralCoveringOwnerDiscovery.outgoing L (metadata G C D R L input v) = lightSupport G C D R L v :=
  GeneralCoveringOwnerDiscovery.outgoing_correct G C D R L _ v rfl rfl rfl

theorem accept_expected (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (i r : V) :
    GeneralCoveringOwnerDiscovery.accept i (GeneralCoveringOwnerDiscovery.makeReport Δ
      (supportUnion G C D R L r) (metadata G C D R L input r)) =
      if GeneralCoveringOwners.owner C D R r = some i then PrefixSet.take (Δ + 1) (uncapped G C D R L i r) else ∅ := by
  cases ho : GeneralCoveringOwners.owner C D R r with
  | none => simp [GeneralCoveringOwnerDiscovery.accept, GeneralCoveringOwnerDiscovery.makeReport,
      metadata, GeneralCoveringOwnerSupport.expected, ho]
  | some d =>
    by_cases he : d = i <;>
      simp [GeneralCoveringOwnerDiscovery.accept, GeneralCoveringOwnerDiscovery.makeReport,
        metadata, GeneralCoveringOwnerSupport.expected, ho, he, uncapped]

theorem raw_expected (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (i : V) :
    (closed G i).biUnion (fun r => GeneralCoveringOwnerDiscovery.accept i
      (GeneralCoveringOwnerDiscovery.makeReport Δ (supportUnion G C D R L r) (metadata G C D R L input r))) =
      PrefixSet.union (family G C D R L i) (Δ + 1) := by
  ext j
  simp only [PrefixSet.union, family, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, hj⟩
    rw [accept_expected G C D R L Δ input i r] at hj
    by_cases ho : GeneralCoveringOwners.owner C D R r = some i
    · have hm : j ∈ PrefixSet.take (Δ + 1) (uncapped G C D R L i r) := by
        simpa only [if_pos ho] using hj
      exact ⟨uncapped G C D R L i r, ⟨r, Finset.mem_filter.mpr ⟨hr, ho⟩, rfl⟩, hm⟩
    · exact False.elim (Finset.notMem_empty j (by simpa only [if_neg ho] using hj))
  · rintro ⟨s, ⟨r, hr, rfl⟩, hj⟩
    have hc := (Finset.mem_filter.mp hr).1
    have ho := (Finset.mem_filter.mp hr).2
    have he := (accept_expected G C D R L Δ input i r).trans (if_pos ho)
    exact ⟨r, hc, he.symm ▸ hj⟩

theorem snapshot_family (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (i : V) :
    GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) i =
      GeneralCoveringOwnerDiscovery.finish Δ i (PrefixSet.union (family G C D R L i) (Δ + 1))
        (metadata G C D R L input i) := by
  have hout : (fun u => GeneralCoveringOwnerDiscovery.outgoing L (metadata G C D R L input u)) =
      lightSupport G C D R L := funext (metadata_outgoing G C D R L input)
  unfold GeneralCoveringOwnerDiscovery.snapshot
  simp only [hout]
  exact congrArg (fun raw => GeneralCoveringOwnerDiscovery.finish Δ i raw (metadata G C D R L input i))
    (raw_expected G C D R L Δ input i)

theorem snapshot_center (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D)) (i : D) :
    GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) i.val =
      ⟨metadata G C D R L input i.val, capped G C D R L Δ i.val,
        decide (Δ < (capped G C D R L Δ i.val).card)⟩ := by
  rw [snapshot_family G C D R L Δ input i.val]
  have he : GeneralCoveringOwnerDiscovery.enabled i.val (metadata G C D R L input i.val) = true := by
    simp [GeneralCoveringOwnerDiscovery.enabled, metadata, GeneralCoveringOwnerSupport.expected,
      hD, i.property, GeneralCoveringOwners.owner_center C D R i.property]
  simp [GeneralCoveringOwnerDiscovery.finish, he, capped]

theorem snapshot_noncenter (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) (hc : (input v).center = false) :
    GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) v =
      ⟨metadata G C D R L input v, ∅, false⟩ :=
  GeneralCoveringOwnerDiscovery.finish_noncenter Δ v _ _ hc

theorem snapshot_none (C : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) (ho : GeneralCoveringOwners.owner C D R v = none) :
    GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) v =
      ⟨metadata G C D R L input v, ∅, false⟩ :=
  GeneralCoveringOwnerDiscovery.finish_none Δ v _ _ ho

/-- Correctness of the unchanged encoded six-round PRIVATE program. No
metadata consistency, neighbor set or degree flag is supplied as input. -/
theorem private_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (D R : Finset V) (L Δ : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (input : V → GeneralCoveringOwners.Input V)
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v) :
    let out := (GeneralCoveringOwnerDiscovery.program ids L Δ).runEncoded G input
    (∀ v, (out v).metadata = metadata G C D R L input v) ∧
    (∀ v, (out v).metadata.owned.input = input v) ∧
    (∀ i : D, (out i.val).neighbors = capped G C D R L Δ i.val ∧
      (out i.val).high = decide (Δ < (ownerGraph G C D R L).degree i) ∧
      (out i.val).neighbors ⊆ neighbors G C D R L i ∧
      ((ownerGraph G C D R L).degree i ≤ Δ → (out i.val).neighbors = neighbors G C D R L i)) ∧
    (∀ v ∉ D, out v = ⟨metadata G C D R L input v, ∅, false⟩) ∧
    (∀ v, GeneralCoveringOwners.owner C D R v = none → out v = ⟨metadata G C D R L input v, ∅, false⟩) := by
  let out := (GeneralCoveringOwnerDiscovery.program ids L Δ).runEncoded G input
  have hr : out = GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) :=
    (GeneralCoveringOwnerDiscovery.program_encoded G ids L Δ input).trans
      (GeneralCoveringOwnerDiscovery.private_snapshot G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    calc
      _ = (GeneralCoveringOwnerDiscovery.snapshot G L Δ (metadata G C D R L input) v).metadata :=
        congrArg GeneralCoveringOwnerDiscovery.Output.metadata (congrFun hr v)
      _ = metadata G C D R L input v := GeneralCoveringOwnerDiscovery.finish_metadata Δ v _ _
  · intro v
    change (((GeneralCoveringOwnerDiscovery.program ids L Δ).runEncoded G input) v).metadata.owned.input = _
    rw [GeneralCoveringOwnerDiscovery.program_encoded]
    exact GeneralCoveringOwnerDiscovery.private_input_retained G ids L Δ input v
  · intro i
    have he : out i.val = ⟨metadata G C D R L input i.val, capped G C D R L Δ i.val,
        decide (Δ < (capped G C D R L Δ i.val).card)⟩ :=
      (congrFun hr i.val).trans (snapshot_center G C D R L Δ input hD i)
    have hns : (out i.val).neighbors = capped G C D R L Δ i.val :=
      congrArg GeneralCoveringOwnerDiscovery.Output.neighbors he
    refine ⟨hns, ?_, ?_, ?_⟩
    · exact (congrArg GeneralCoveringOwnerDiscovery.Output.high he).trans
        (Bool.decide_congr (capped_high G C D R L Δ hlocal i))
    · exact hns.symm ▸ capped_subset G C D R L Δ hlocal i
    · intro hlow
      exact hns.trans (capped_low G C D R L Δ hlocal i hlow)
  · intro v hv
    have hc : (input v).center = false := by simp [hD v, hv]
    exact (congrFun hr v).trans (snapshot_noncenter G C D R L Δ input v hc)
  · intro v ho
    exact (congrFun hr v).trans (snapshot_none G C D R L Δ input v ho)

end Paper.GeneralCoveringOwnerDiscoveryCorrect

#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.family_union
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.root_neighbors
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.family_neighbors
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.card_family
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.capped_subset
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.capped_high
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.capped_low
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.metadata_outgoing
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.accept_expected
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.raw_expected
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.snapshot_family
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.snapshot_center
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.snapshot_noncenter
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.snapshot_none
#print axioms Paper.GeneralCoveringOwnerDiscoveryCorrect.private_correct
