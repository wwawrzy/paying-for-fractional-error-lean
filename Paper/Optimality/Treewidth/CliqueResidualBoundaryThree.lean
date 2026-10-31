import Paper.Optimality.Treewidth.CliqueResidualCanonical
import Paper.Optimality.Treewidth.CliqueTwoOutsideForced
import Paper.Optimality.Treewidth.CliqueCommonTransport
import Paper.Optimality.Treewidth.SevenCliqueUniversalContact
namespace Paper.CliqueResidualBoundaryThree
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem bound (T : Finset V) (hT : T.card = 8)
    (e : (G.induce (T : Set V)) ≃g CliqueEightResidualTemplates.graph 0 1)
    (hdegree : ∀ z ∈ T, G.degree z = 8)
    (hcn : ∀ a z, G.Adj a z → 5 ≤ Fintype.card (G.commonNeighbors a z))
    (hreg : ∀ a ∈ T, ∀ z ∈ T, G.Adj a z → G.inducedDegree z (G.neighborFinset a) = 5) :
    (CliqueComponentBoundary.boundary G (T : Set V)).card ≤ 3 := by
  classical
  let F := CliqueEightResidualTemplates.graph 0 1
  let f : Fin 8 → V := fun i => (e.symm i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hmem : ∀ i, f i ∈ T := fun i => (e.symm i).property
  have hinner : ∀ i, G.inducedDegree (f i) T = F.degree i := by
    intro i
    rw [← InducedCounting.degree_induce_eq_inducedDegree G T (e.symm i)]
    exact e.symm.degree_eq i
  have hadj : ∀ i j, G.Adj (f i) (f j) ↔ F.Adj i j := by
    intro i j
    exact e.symm.map_rel_iff
  have hout : ∀ i, G.inducedDegree (f i) Tᶜ + F.degree i = 8 := by
    intro i
    have hh := CliquePartitionDegrees.partition G T (f i)
    rw [hinner,hdegree _ (hmem i)] at hh
    omega
  have hc : ∀ i j, (T.filter (fun y => G.Adj (f i) y ∧ G.Adj (f j) y)).card = Fintype.card (F.commonNeighbors i j) := by
    intro i j
    rw [CliqueCommonTransport.induced_card G T (e.symm i) (e.symm j)]
    have hh := CliqueCommonTransport.iso_card _ _ e (e.symm i) (e.symm j)
    simpa only [e.apply_symm_apply] using hh
  have h7 : G.inducedDegree (f 7) T = 7 := (hinner 7).trans (by decide)
  have h6 : ∀ i : Fin 8, i = 5 ∨ i = 6 → G.inducedDegree (f i) T = 6 := by
    intro i hi
    rcases hi with rfl | rfl <;> exact (hinner _).trans (by decide)
  have hcycle : ∀ i : Fin 8, i.val < 5 → G.inducedDegree (f i) T = 5 := by
    intro i hi
    exact (hinner i).trans (Paper.CliqueResidualCanonical.cycle_data i hi).1
  have h71 : G.inducedDegree (f 7) Tᶜ = 1 := by have hh := hout 7; change _ + 7 = 8 at hh; omega
  obtain ⟨p,hp,hxp,hunique⟩ := Paper.SevenCliqueTwentySixClassification.unique_outside G T (f 7) h71
  have hpcycle : ∀ i : Fin 8, i.val < 5 → G.Adj p (f i) := by
    intro i hi
    have hxi : G.Adj (f 7) (f i) := by
      apply CliqueForcedExteriorContact.universal_inside G T (f 7) (hmem 7) hT h7 (f i) (hmem i)
      exact hf.ne (by intro h; have := congrArg Fin.val h; omega)
    exact CliqueForcedExteriorContact.forced G T (f 7) p (f i) (hmem 7) hxi hunique (hcycle i hi) (hcn _ _ hxi)
  have hpno : ∀ i : Fin 8, i = 5 ∨ i = 6 → ¬G.Adj p (f i) := by
    intro i hi
    have hxi : G.Adj (f 7) (f i) := by rw [hadj]; rcases hi with rfl | rfl <;> decide
    exact CliqueTwoOutsideForced.not_contact G T (f 7) p (f i) (hmem 7) (hmem i) h7 hT (h6 i hi) hp hxp
      (hreg _ (hmem 7) _ (hmem i) hxi)
  have htwo : G.inducedDegree (f 5) Tᶜ = 2 := by have hh := hout 5; change _ + 6 = 8 at hh; omega
  obtain ⟨r,s,hrs,hO⟩ := Finset.card_eq_two.mp htwo
  have hOmem : ∀ q, (q ∉ T ∧ G.Adj (f 5) q) ↔ q = r ∨ q = s := by
    intro q
    have hh := Finset.ext_iff.mp hO q
    simpa only [Finset.mem_filter,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton] using hh
  have hr := (hOmem r).mpr (Or.inl rfl)
  have hs := (hOmem s).mpr (Or.inr rfl)
  have hpr : p ≠ r := by intro heq; exact hpno 5 (Or.inl rfl) (heq ▸ hr.2.symm)
  have hps : p ≠ s := by intro heq; exact hpno 5 (Or.inl rfl) (heq ▸ hs.2.symm)
  have hall : ∀ a : Fin 8, a = 5 ∨ a = 6 → ∀ i : Fin 8, i.val < 5 →
      ∀ q, q ∉ T → G.Adj (f a) q → G.Adj q (f i) := by
    intro a ha i hi q hq haq
    have hda : G.inducedDegree (f a) Tᶜ = 2 := by have hh := hout a; rw [← hinner,h6 a ha] at hh; omega
    have hai : G.Adj (f a) (f i) := by
      rw [hadj]
      rcases ha with rfl | rfl
      · exact (CliqueResidualCanonical.cycle_data i hi).2.1
      · exact (CliqueResidualCanonical.cycle_data i hi).2.2.1
    have hci : (T.filter (fun y => G.Adj (f a) y ∧ G.Adj (f i) y)).card ≤ 3 := by
      rw [hc]
      rcases ha with rfl | rfl
      · exact (CliqueResidualCanonical.cycle_data i hi).2.2.2.1.le
      · exact (CliqueResidualCanonical.cycle_data i hi).2.2.2.2.le
    exact CliqueTwoOutsideForced.forced G T (f a) (f i) hda hci (hcn _ _ hai) q hq haq
  have hcycleO : ∀ i : Fin 8, i.val < 5 → ∀ q, q ∉ T → G.Adj (f i) q → q ∈ ({p,r,s} : Finset V) := by
    intro i hi
    have hdi : G.inducedDegree (f i) Tᶜ = 3 := by have hh := hout i; rw [← hinner,hcycle i hi] at hh; omega
    have hsub : ({p,r,s} : Finset V) ⊆ Tᶜ.filter (G.Adj (f i)) := by
      intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hp,(hpcycle i hi).symm⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hr.1,(hall 5 (Or.inl rfl) i hi q hr.1 hr.2).symm⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hs.1,(hall 5 (Or.inl rfl) i hi q hs.1 hs.2).symm⟩
    have heq : ({p,r,s} : Finset V) = Tᶜ.filter (G.Adj (f i)) := by
      apply Finset.eq_of_subset_of_card_le hsub
      have hcard : ({p,r,s} : Finset V).card = 3 := by simp [hpr,hps,hrs]
      change G.inducedDegree (f i) Tᶜ ≤ _
      omega
    intro q hq hiq
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hq,hiq⟩
  have hbound : CliqueComponentBoundary.boundary G (T : Set V) ⊆ {p,r,s} := by
    intro q hq
    obtain ⟨hq,z,hz,hqz⟩ := (CliqueComponentBoundary.mem_boundary G _ q).mp hq
    let i := e ⟨z,hz⟩
    have hiz : f i = z := by exact congrArg Subtype.val (e.symm_apply_apply ⟨z,hz⟩)
    have hzi : G.Adj (f i) q := hiz.symm ▸ hqz.symm
    have hqT : q ∉ T := hq
    by_cases hi : i.val < 5
    · exact hcycleO i hi q hqT hzi
    · have hcases : i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases hcases with h5 | h6 | h7
      · rw [h5] at hzi
        have hh := (hOmem q).mp ⟨hqT,hzi⟩
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      · rw [h6] at hzi
        exact hcycleO 0 (by decide) q hqT (hall 6 (Or.inr rfl) 0 (by decide) q hqT hzi).symm
      · rw [h7] at hzi
        have hh := hunique q hqT hzi
        simp [hh]
  exact (Finset.card_le_card hbound).trans (Finset.card_le_three)
end Paper.CliqueResidualBoundaryThree
