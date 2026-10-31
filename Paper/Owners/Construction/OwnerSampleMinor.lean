import Paper.Owners.Construction.OwnerExperiment

/-! Every outcome of the owner experiment is an actual physical minor.
Attached vertices reach their selected owner through a selected-star vertex. -/
namespace Paper.OwnerSampleMinor
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport OwnerExperiment
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def model {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) :
    SimpleGraph.MinorModel (OwnerExperiment.graph G D R L ω) G where
  branchSet a := {v | label G D R L ω v = some a.val}
  nonempty a := ⟨a.val, label_center G D R L ω a.property⟩
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    exact hab (Subtype.ext (Option.some.inj (ha.symm.trans hb)))
  connected a := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let root : {v // label G D R L ω v = some a.val} := ⟨a.val, label_center G D R L ω a.property⟩
    refine ⟨root, ?_⟩
    have base : ∀ u (hu : owner G D u = a.val),
        ∃ hlabel : label G D R L ω u = some a.val,
          (G.induce {v | label G D R L ω v = some a.val}).Reachable root ⟨u, hlabel⟩ := by
      intro u hu
      have hl : label G D R L ω u = some a.val := by
        have hm : owner G D u ∈ sampled D ω := hu ▸ a.property
        simpa only [hu] using label_base G D R L ω hm
      refine ⟨hl, ?_⟩
      rcases owner_star G D u with he | ha
      · have hv : root = (⟨u, hl⟩ : {v // label G D R L ω v = some a.val}) :=
          Subtype.ext (hu.symm.trans he)
        rw [hv]
        exact SimpleGraph.Reachable.refl _
      · have ha' : G.Adj a.val u := by rwa [hu] at ha
        exact (show (G.induce {v | label G D R L ω v = some a.val}).Adj root ⟨u, hl⟩ from ha').reachable
    intro v
    rcases label_cases G D R L ω v.property with hb | ha
    · obtain ⟨hl, hr⟩ := base v.val hb.1
      exact hr
    · obtain ⟨u, hu, hud⟩ := Finset.mem_image.mp ha.2.1
      obtain ⟨hl, hr⟩ := base u hud
      have hc := (Finset.mem_inter.mp hu).1
      rcases (mem_closed G u v.val).mp hc with he | hadj
      · simpa only [he] using hr
      · have hadj' : (G.induce {v | label G D R L ω v = some a.val}).Adj ⟨u, hl⟩ v := hadj.symm
        exact hr.trans hadj'.reachable
  adjacent a b hab := by
    obtain ⟨_, u, v, hu, hv, ha⟩ := hab
    exact ⟨u, hu, v, hv, ha⟩

theorem density {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    ((OwnerExperiment.graph G D R L ω).edgeFinset.card : ℝ) ≤ a * D.card := by
  classical
  have hh := hden (sampled D ω) (OwnerExperiment.graph G D R L ω) ⟨model G D R L ω⟩
  have hc : Fintype.card (sampled D ω) ≤ D.card := by
    rw [Fintype.card_coe]
    exact Finset.card_filter_le _ _
  have hc' : (Fintype.card (sampled D ω) : ℝ) ≤ D.card := by exact_mod_cast hc
  exact hh.trans (mul_le_mul_of_nonneg_left hc' ha)
end Paper.OwnerSampleMinor
