import Paper.Solver.LocalSearch.GeneralCoveringOwnerSupport

/-! Actual partners after the arbitrary-covering owner/support protocol.
A residual center without self-incidence chooses min(D intersect C(i)) from
one real center-bit broadcast. The preserved state contains all original
private fields and the previously computed supports/residual bits. -/
namespace Paper.GeneralCoveringPartners
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

structure Output (V : Type) where
  state : GeneralCoveringOwnerSupport.State V
  partner : Option V

def round : Round V (GeneralCoveringOwnerSupport.State V) (Output V) Bool where
  send _ _ s := s.owned.input.center
  update v N s msg := ⟨s, if s.owned.input.center = true ∧ s.residual = true ∧
      v ∉ s.owned.input.candidates then
    MaskedMinimum.minimum (FlagNeighborhood.selected v N s.owned.input.center msg ∩
      s.owned.input.candidates) else none⟩

def attach : Program V (GeneralCoveringOwnerSupport.State V) (Output V) :=
  .broadcast 1 BitCode.bool round

def program {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V) :=
  .seq (GeneralCoveringOwnerSupport.program ids L) attach

/-- All public parameters precede the graph; all partner prerequisites are
computed by the accepted initializer/owner/support programs. -/
def initialized {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    Program V (GeneralCoveringInitializerRun.Input V) (Output V) :=
  .seq (GeneralCoveringOwnerSupport.initialized ids b h f T L) attach

theorem attach_rounds : (attach (V := V)).rounds = 1 := rfl

theorem attach_maxBits : (attach (V := V)).maxBits = 1 := rfl

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (program ids L).rounds = 5 := rfl

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (program ids L).maxBits = bits + 1 := by
  simpa only [program, Program.maxBits, GeneralCoveringOwnerSupport.maxBits, attach_maxBits]
    using (max_eq_left (by omega : 1 ≤ bits + 1))

variable [Fintype V]

theorem initialized_rounds {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    (initialized ids b h f T L).rounds = T * (5 + 2 * f) + 7 := by
  simp only [initialized, Program.rounds, GeneralCoveringOwnerSupport.initialized_rounds, attach_rounds]

theorem initialized_maxBits {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    (initialized ids b h f T L).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
  simp only [initialized, Program.maxBits, attach_maxBits]
  exact max_le (GeneralCoveringOwnerSupport.initialized_maxBits ids b h f T L)
    ((by omega : 1 ≤ bits + 1).trans (le_max_left _ _))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def partner (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : V) : Option V :=
  if i ∈ D ∧ i ∈ GeneralCoveringOwnerSupport.residual G C D R L ∧ i ∉ C i then
    MaskedMinimum.minimum (D ∩ C i) else none

theorem some_spec (C : V → Finset V) (D R : Finset V) (L : ℕ) {i v : V}
    (hp : partner G C D R L i = some v) :
    i ∈ D ∧ i ∈ GeneralCoveringOwnerSupport.residual G C D R L ∧ i ∉ C i ∧ v ∈ D ∩ C i := by
  unfold partner at hp
  split_ifs at hp with hn
  · exact ⟨hn.1, hn.2.1, hn.2.2, MaskedMinimum.minimum_mem hp⟩

theorem exists_partner (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) {i : V} (hi : i ∈ D)
    (hr : i ∈ GeneralCoveringOwnerSupport.residual G C D R L) (hnot : i ∉ C i) :
    ∃ v ∈ D ∩ C i, partner G C D R L i = some v := by
  obtain ⟨u, huD, huC⟩ := hcover i (Finset.mem_filter.mp hr).1
  obtain ⟨v, hv, _⟩ := MaskedMinimum.minimum_le (Finset.mem_inter.mpr ⟨huD, huC⟩)
  have hcond : i ∈ D ∧ i ∈ GeneralCoveringOwnerSupport.residual G C D R L ∧ i ∉ C i :=
    ⟨hi, hr, hnot⟩
  exact ⟨v, MaskedMinimum.minimum_mem hv, by simp only [partner, if_pos hcond, hv]⟩

theorem minimum (C : V → Finset V) (D R : Finset V) (L : ℕ) {i v : V}
    (hp : partner G C D R L i = some v) : ∀ u ∈ D ∩ C i, v ≤ u := by
  have hs := some_spec G C D R L hp
  have hcond : i ∈ D ∧ i ∈ GeneralCoveringOwnerSupport.residual G C D R L ∧ i ∉ C i :=
    ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hm : MaskedMinimum.minimum (D ∩ C i) = some v := by
    simpa only [partner, if_pos hcond] using hp
  intro u hu
  obtain ⟨w, hw, hle⟩ := MaskedMinimum.minimum_le hu
  have he : v = w := Option.some.inj (hm.symm.trans hw)
  simpa only [he] using hle

theorem ne_self (C : V → Finset V) (D R : Finset V) (L : ℕ) {i v : V}
    (hp : partner G C D R L i = some v) : v ≠ i := by
  have hs := some_spec G C D R L hp
  intro he
  exact hs.2.2.1 (he ▸ (Finset.mem_inter.mp hs.2.2.2).2)

theorem adjacent (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {i v : V}
    (hp : partner G C D R L i = some v) : G.Adj i v := by
  have hs := some_spec G C D R L hp
  have hvC := (Finset.mem_inter.mp hs.2.2.2).2
  have hvclosed := hlocal i (Finset.mem_filter.mp hs.2.1).1 hvC
  exact ((mem_closed G v i).mp hvclosed).resolve_left (ne_self G C D R L hp)

theorem light_admissible (C : V → Finset V) (D R : Finset V) (L : ℕ) {i v : V}
    (hp : partner G C D R L i = some v) :
    v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
      (GeneralCoveringOwnerSupport.support G C D R v).card ≤ L := by
  have hs := some_spec G C D R L hp
  exact GeneralCoveringOwnerSupport.residual_candidates G C D R L hs.2.1
    (Finset.mem_inter.mp hs.2.2.2).2

theorem owner_in_support (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {i v : V}
    (hp : partner G C D R L i = some v) : i ∈ GeneralCoveringOwnerSupport.support G C D R v := by
  have hs := some_spec G C D R L hp
  exact GeneralCoveringOwnerSupport.incidence_label G C D R hlocal
    (Finset.mem_filter.mp hs.2.1).1 (Finset.mem_inter.mp hs.2.2.2).2
    (GeneralCoveringOwners.owner_center C D R hs.1)

noncomputable def preimages (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  Finset.univ.filter (fun i => partner G C D R L i = some v)

theorem preimages_subset (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (v : V) :
    preimages G C D R L v ⊆ GeneralCoveringOwnerSupport.support G C D R v := by
  intro i hi
  exact owner_in_support G C D R L hlocal (Finset.mem_filter.mp hi).2

theorem preimages_card (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (v : V) : (preimages G C D R L v).card ≤ L := by
  by_cases hn : (preimages G C D R L v).Nonempty
  · obtain ⟨i, hi⟩ := hn
    have hp := (Finset.mem_filter.mp hi).2
    exact (Finset.card_le_card (preimages_subset G C D R L hlocal v)).trans
      (light_admissible G C D R L hp).2.2
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [he, Finset.card_empty] using (Nat.zero_le L)

noncomputable def bundle (C : V → Finset V) (D R : Finset V) (L : ℕ) (i : V) : Finset V :=
  {i} ∪ (partner G C D R L i).toFinset

/-- An owner alone covers every noncentral demand in its class. A residual
center uses self-incidence if present and its partner otherwise. -/
theorem bundle_covers (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) {i r : V} (hi : i ∈ D)
    (hr : r ∈ GeneralCoveringOwnerSupport.residual G C D R L)
    (ho : GeneralCoveringOwners.owner C D R r = some i) :
    ∃ v ∈ bundle G C D R L i, v ∈ C r := by
  by_cases hrD : r ∈ D
  · have he : r = i := Option.some.inj ((GeneralCoveringOwners.owner_center C D R hrD).symm.trans ho)
    subst r
    by_cases hiC : i ∈ C i
    · exact ⟨i, Finset.mem_union_left _ (Finset.mem_singleton_self i), hiC⟩
    · obtain ⟨v, hv, hp⟩ := exists_partner G C D R L hcover hi hr hiC
      exact ⟨v, Finset.mem_union_right _ (by simp [hp]), (Finset.mem_inter.mp hv).2⟩
  · exact ⟨i, Finset.mem_union_left _ (Finset.mem_singleton_self i),
      (Finset.mem_inter.mp (GeneralCoveringOwners.owner_incidence C D R
        (Finset.mem_filter.mp hr).1 hrD ho)).2⟩

theorem bundle_cost_eq (C : V → Finset V) (D R : Finset V) (L : ℕ) (c : V → ℝ) (i : V) :
    (∑ v ∈ bundle G C D R L i, c v) = c i + ∑ v ∈ (partner G C D R L i).toFinset, c v := by
  have hn : i ∉ (partner G C D R L i).toFinset := by
    intro hi
    have hp : partner G C D R L i = some i := by simpa using hi
    exact ne_self G C D R L hp rfl
  rw [bundle, Finset.sum_union (Finset.disjoint_singleton_left.mpr hn), Finset.sum_singleton]

theorem multiplicity_cost (C : V → Finset V) (D R : Finset V) (L B : ℕ) (c : V → ℝ)
    (hD : D ⊆ CoveringSupport.admissible C R) {i : V} (hi : i ∈ D)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    c i + (∑ v ∈ (partner G C D R L i).toFinset, c v) ≤ 2 * (B : ℝ) := by
  have hci := hc i (hD hi)
  have hpi : (∑ v ∈ (partner G C D R L i).toFinset, c v) ≤ (B : ℝ) := by
    cases hp : partner G C D R L i with
    | none => simpa only [hp, Option.toFinset_none, Finset.sum_empty] using (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
    | some v => simpa [hp] using hc v (light_admissible G C D R L hp).1
  linarith

theorem bundle_cost (C : V → Finset V) (D R : Finset V) (L B : ℕ) (c : V → ℝ)
    (hD : D ⊆ CoveringSupport.admissible C R) {i : V} (hi : i ∈ D)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    (∑ v ∈ bundle G C D R L i, c v) ≤ 2 * (B : ℝ) := by
  calc
    _ = c i + ∑ v ∈ (partner G C D R L i).toFinset, c v := bundle_cost_eq G C D R L c i
    _ ≤ _ := multiplicity_cost G C D R L B c hD hi hc

/-- This sum retains shared partners with multiplicity, as required later
by the owner/boundary expectation formula. -/
theorem owners_cost (C : V → Finset V) (D R : Finset V) (L B : ℕ) (c : V → ℝ)
    (hD : D ⊆ CoveringSupport.admissible C R) (I : Finset V) (hI : I ⊆ D)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    (∑ i ∈ I, (c i + ∑ v ∈ (partner G C D R L i).toFinset, c v)) ≤ 2 * (B : ℝ) * I.card := by
  calc
    _ ≤ ∑ _i ∈ I, (2 * (B : ℝ)) :=
      Finset.sum_le_sum (fun i hi => multiplicity_cost G C D R L B c hD (hI hi) hc)
    _ = _ := by simp [mul_comm]

/-- Correctness of the literal extra center-bit broadcast. Only a true
residual row needs locality, and its residual bit was already computed. -/
theorem attach_correct (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V)
    (hD : ∀ i, (s i).owned.input.center = decide (i ∈ D))
    (hr : ∀ i, (s i).residual = decide (i ∈ GeneralCoveringOwnerSupport.residual G C D R L))
    (hC : ∀ i, (s i).owned.input.candidates = C i)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    attach.run G s = fun i => ⟨s i, partner G C D R L i⟩ := by
  funext i
  have hnear := FlagNeighborhood.correct G D i
  change FlagNeighborhood.selected i (G.neighborFinset i) (decide (i ∈ D))
    (fun u => decide (u.val ∈ D)) = closed G i ∩ D at hnear
  change (⟨s i, if (s i).owned.input.center = true ∧ (s i).residual = true ∧
      i ∉ (s i).owned.input.candidates then
    MaskedMinimum.minimum (FlagNeighborhood.selected i (G.neighborFinset i) (s i).owned.input.center
      (fun u => (s u.val).owned.input.center) ∩ (s i).owned.input.candidates) else none⟩ : Output V) = _
  simp only [hD, hr, hC, decide_eq_true_eq]
  rw [hnear]
  by_cases hn : i ∈ D ∧ i ∈ GeneralCoveringOwnerSupport.residual G C D R L ∧ i ∉ C i
  · have hiR := (Finset.mem_filter.mp hn.2.1).1
    have he : (closed G i ∩ D) ∩ C i = D ∩ C i := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, hvD⟩, hvC⟩
        exact ⟨hvD, hvC⟩
      · rintro ⟨hvD, hvC⟩
        exact ⟨⟨hlocal i hiR hvC, hvD⟩, hvC⟩
    simp only [partner, if_pos hn, he]
  · simp only [partner, if_neg hn]

theorem correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → GeneralCoveringOwners.Input V)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ r, (s r).demand = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    (program ids L).run G s = fun i =>
      ⟨GeneralCoveringOwnerSupport.expected G C D R L
        (fun v => ⟨s v, GeneralCoveringOwners.owner C D R v⟩) i, partner G C D R L i⟩ := by
  change attach.run G ((GeneralCoveringOwnerSupport.program ids L).run G s) = _
  rw [GeneralCoveringOwnerSupport.correct G ids C targets D R L hinc hlocal s hD hR hC hTargets]
  exact attach_correct G C D R L _ hD (fun _ => rfl) hC hlocal

theorem initialized_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T L : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    let t := GeneralCoveringOwnerSupport.expected G C D R L (fun v =>
      ⟨GeneralCoveringOwners.initializerInput ⟨decide (v ∈ D), false⟩ (s v),
        GeneralCoveringOwners.owner C D R v⟩)
    (initialized ids b h f T L).run G s = fun i => ⟨t i, partner G C D R L i⟩ := by
  change attach.run G ((GeneralCoveringOwnerSupport.initialized ids b h f T L).run G s) = _
  rw [GeneralCoveringOwnerSupport.initialized_correct G ids C targets b h f T L hb R
    hinc hlocal hrows s hR hC hTargets]
  exact attach_correct G C (GeneralCoveringInitializerRun.selected C b h f R T) R L _
    (fun _ => rfl) (fun _ => rfl) hC hlocal

theorem initialized_encoded {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T L : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    let t := GeneralCoveringOwnerSupport.expected G C D R L (fun v =>
      ⟨GeneralCoveringOwners.initializerInput ⟨decide (v ∈ D), false⟩ (s v),
        GeneralCoveringOwners.owner C D R v⟩)
    (initialized ids b h f T L).runEncoded G s = fun i => ⟨t i, partner G C D R L i⟩ := by
  rw [Program.runEncoded_eq_run]
  exact initialized_correct G ids C targets b h f T L hb R hinc hlocal hrows s hR hC hTargets

/-- The bound refers to the computed output's own S0, rather than a
separately supplied support set. -/
theorem initialized_preimages {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T L : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let out := (initialized ids b h f T L).run G s
    ∀ v, (Finset.univ.filter (fun i => (out i).partner = some v)) ⊆ (out v).state.support ∧
      (Finset.univ.filter (fun i => (out i).partner = some v)).card ≤ L := by
  dsimp only
  rw [initialized_correct G ids C targets b h f T L hb R hinc hlocal hrows s hR hC hTargets]
  intro v
  exact ⟨preimages_subset G C (GeneralCoveringInitializerRun.selected C b h f R T) R L hlocal v,
    preimages_card G C (GeneralCoveringInitializerRun.selected C b h f R T) R L hlocal v⟩

/-- Actual computed partners cover every residual member of each owner class,
and the per-owner cost bound keeps the optional partner with multiplicity. -/
theorem initialized_bundles {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T L B : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v)
    (c : V → ℝ) (hc : ∀ v ∈ CoveringSupport.admissible C R, c v ≤ B) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    let out := (initialized ids b h f T L).run G s
    ∀ i ∈ D, (c i + ∑ v ∈ (out i).partner.toFinset, c v) ≤ 2 * (B : ℝ) ∧
      ∀ r, (out r).state.residual = true → (out r).state.owned.owner = some i →
        ∃ v ∈ ({i} ∪ (out i).partner.toFinset), v ∈ C r := by
  dsimp only
  rw [initialized_correct G ids C targets b h f T L hb R hinc hlocal hrows s hR hC hTargets]
  intro i hi
  constructor
  · exact multiplicity_cost G C (GeneralCoveringInitializerRun.selected C b h f R T) R L B c
      (GeneralCoveringInitializerRun.selected_admissible C b h f hb R T) hi hc
  · intro r hr ho
    exact bundle_covers G C (GeneralCoveringInitializerRun.selected C b h f R T) R L
      (GeneralCoveringInitializerRun.selected_covers C b h f R T hrows) hi (of_decide_eq_true hr) ho

end Paper.GeneralCoveringPartners

#print axioms Paper.GeneralCoveringPartners.some_spec
#print axioms Paper.GeneralCoveringPartners.exists_partner
#print axioms Paper.GeneralCoveringPartners.minimum
#print axioms Paper.GeneralCoveringPartners.ne_self
#print axioms Paper.GeneralCoveringPartners.adjacent
#print axioms Paper.GeneralCoveringPartners.light_admissible
#print axioms Paper.GeneralCoveringPartners.owner_in_support
#print axioms Paper.GeneralCoveringPartners.preimages_subset
#print axioms Paper.GeneralCoveringPartners.preimages_card
#print axioms Paper.GeneralCoveringPartners.bundle_covers
#print axioms Paper.GeneralCoveringPartners.bundle_cost_eq
#print axioms Paper.GeneralCoveringPartners.multiplicity_cost
#print axioms Paper.GeneralCoveringPartners.bundle_cost
#print axioms Paper.GeneralCoveringPartners.owners_cost
#print axioms Paper.GeneralCoveringPartners.attach_correct
#print axioms Paper.GeneralCoveringPartners.correct
#print axioms Paper.GeneralCoveringPartners.initialized_correct
#print axioms Paper.GeneralCoveringPartners.initialized_encoded
#print axioms Paper.GeneralCoveringPartners.initialized_preimages
#print axioms Paper.GeneralCoveringPartners.initialized_bundles
#print axioms Paper.GeneralCoveringPartners.rounds
#print axioms Paper.GeneralCoveringPartners.maxBits
#print axioms Paper.GeneralCoveringPartners.initialized_rounds
#print axioms Paper.GeneralCoveringPartners.initialized_maxBits
