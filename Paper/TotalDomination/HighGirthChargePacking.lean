import Paper.TotalDomination.HighGirthFreePathEnds

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem component_member_unique
    (C D : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    {u : V} (hC : u ∈ componentMembers G x identifier hfree C)
    (hD : u ∈ componentMembers G x identifier hfree D) : C = D := by
  classical
  obtain ⟨hu,huc⟩ := (Finset.mem_filter.mp hC).2
  obtain ⟨_,hud⟩ := (Finset.mem_filter.mp hD).2
  exact huc.symm.trans hud

theorem positive_charge_component_unique
    (C D : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (hD : freeComponent G x identifier hfree D)
    (hx : ∀ v, 0 ≤ x v) {v : V}
    (hvC : v ∈ freeTerms G x identifier hfree C) (hvD : v ∈ freeTerms G x identifier hfree D)
    (hpos : 0 < ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v) : C = D := by
  classical
  have hh := (positive_charge_vertex G x identifier hfree C hC hx hvC hpos).2
  obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hvC).2
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hvD).2
  have huR : u ∈ G.neighborFinset v ∩ residual G (I G x identifier hfree) :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1,
      core_residual G x identifier hfree (component_subset_core G x identifier hfree C (Finset.mem_inter.mp hu).2)⟩
  have hzR : z ∈ G.neighborFinset v ∩ residual G (I G x identifier hfree) :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
      core_residual G x identifier hfree (component_subset_core G x identifier hfree D (Finset.mem_inter.mp hz).2)⟩
  change (G.neighborFinset v ∩ residual G (I G x identifier hfree)).card = 1 at hh
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hh
  have hur : u = r := Finset.mem_singleton.mp (hr ▸ huR)
  have hzr : z = r := Finset.mem_singleton.mp (hr ▸ hzR)
  have he : u = z := hur.trans hzr.symm
  rw [← he] at hz
  exact component_member_unique G x identifier hfree C D (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hz).2

theorem component_charge_bound
    (family : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hfamily : ∀ C ∈ family, freeComponent G x identifier hfree C)
    (hx : ∀ v, 0 ≤ x v) :
    (∑ C ∈ family, freeCharge G x identifier hfree C) ≤
      penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) := by
  classical
  let weight := fun v => ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v
  let O := other G (I G x identifier hfree)
  have hnon : ∀ v ∈ O, 0 ≤ weight v := by
    intro v hv
    have hh : (hits G (I G x identifier hfree) v : ℝ) ≤ c G v := by
      exact_mod_cast other_hits_cost G x identifier hfree hv
    exact mul_nonneg (sub_nonneg.mpr hh) (hx v)
  have hQ : ∀ C, freeCharge G x identifier hfree C =
      ∑ v ∈ O, if v ∈ freeTerms G x identifier hfree C then weight v else 0 := by
    intro C
    rw [← Finset.sum_filter]
    have heq : O.filter (fun v => v ∈ freeTerms G x identifier hfree C) = freeTerms G x identifier hfree C := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    rw [heq]
    rfl
  simp_rw [hQ]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v hv
  change (∑ C ∈ family, if v ∈ freeTerms G x identifier hfree C then weight v else 0) ≤ weight v
  by_cases hp : 0 < weight v
  · let Cs := family.filter (fun C => v ∈ freeTerms G x identifier hfree C)
    have hcard : Cs.card ≤ 1 := Finset.card_le_one.mpr (by
      intro C hC D hD
      exact positive_charge_component_unique G x identifier hfree C D
        (hfamily C (Finset.mem_filter.mp hC).1) (hfamily D (Finset.mem_filter.mp hD).1) hx
        (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2 hp)
    rw [← Finset.sum_filter]
    change (∑ _C ∈ Cs, weight v) ≤ weight v
    have hcardR : (Cs.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa only [Finset.sum_const,nsmul_eq_mul,one_mul] using mul_le_mul_of_nonneg_right hcardR (hnon v hv)
  · have hz : weight v = 0 := le_antisymm (le_of_not_gt hp) (hnon v hv)
    simp only [hz,ite_self,Finset.sum_const_zero]
    exact le_rfl

noncomputable def coreOversupply : ℝ :=
  ∑ r ∈ core G x identifier hfree, ((∑ v ∈ G.neighborFinset r, x v)-1)

theorem component_oversupply_bound
    (family : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (∑ C ∈ family, freeOversupply G x identifier hfree C) ≤ coreOversupply G x identifier hfree := by
  classical
  let row := fun r => (∑ v ∈ G.neighborFinset r, x v)-1
  have hdis : (↑family : Set (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent).Pairwise
      (fun C D => Disjoint (componentMembers G x identifier hfree C) (componentMembers G x identifier hfree D)) := by
    intro C hC D hD hne
    apply Finset.disjoint_left.mpr
    intro u huC huD
    exact hne (component_member_unique G x identifier hfree C D huC huD)
  have hsub : family.biUnion (componentMembers G x identifier hfree) ⊆ core G x identifier hfree := by
    intro r hr
    obtain ⟨C,hC,hrC⟩ := Finset.mem_biUnion.mp hr
    exact component_subset_core G x identifier hfree C hrC
  have hrow : ∀ r ∈ core G x identifier hfree, 0 ≤ row r := by
    intro r hr
    exact sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp (core_residual G x identifier hfree hr)).1)
  change (∑ C ∈ family, ∑ r ∈ componentMembers G x identifier hfree C, row r) ≤
    ∑ r ∈ core G x identifier hfree, row r
  calc
    _ = ∑ r ∈ family.biUnion (componentMembers G x identifier hfree), row r := (Finset.sum_biUnion hdis).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => hrow r hr)

/-- Aggregation only: the local one-third charge must still be proved for
all actual nonexceptional bad paths before this is used as fv:hg:t-bad. -/
theorem charged_family_bound
    (family : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hfamily : ∀ C ∈ family, freeComponent G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcharge : ∀ C ∈ family, (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C) :
    (family.card : ℝ) ≤ 3*penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) +
      3*coreOversupply G x identifier hfree := by
  have hQ := component_charge_bound G x identifier hfree family hfamily hx.1
  have hΩ := component_oversupply_bound G x identifier hfree family hx
  have hsum := Finset.sum_le_sum hcharge
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  linarith

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.component_charge_bound
#print axioms Paper.TotalDomination.HighGirthSetup.component_oversupply_bound
