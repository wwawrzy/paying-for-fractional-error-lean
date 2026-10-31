import Paper.Solver.Density.NeighborhoodSlackIncidence

/-! A graph-independent positive neighborhood slack when `2a` is not an
integer. The proof uses actual integer degrees in an induced vertex set and
the density-only weighted-incidence inequality. No orientation is assumed. -/

namespace Paper.Density.NeighborhoodSlack

open SevenFoundation
open scoped BigOperators

structure Parameters where
  a : ℝ
  a_ge_one : 1 ≤ a
  k : ℕ
  theta : ℝ
  decomposition : 2 * a = k + theta
  theta_pos : 0 < theta
  theta_lt_one : theta < 1

noncomputable def cut (p : Parameters) : ℝ :=
  p.theta * (1 - p.theta) / (8 * p.a * ((p.k : ℝ) + 1))

noncomputable def eta (p : Parameters) : ℝ :=
  min (p.theta / 2) (min (cut p) ((1 - p.theta) * cut p / (4 * (2 * p.a))))

theorem cut_pos (p : Parameters) : 0 < cut p := by
  have ha : 0 < p.a := by linarith [p.a_ge_one]
  have hg : 0 < 1 - p.theta := sub_pos.mpr p.theta_lt_one
  have ht := p.theta_pos
  unfold cut
  positivity

theorem eta_pos (p : Parameters) : 0 < eta p := by
  have ha : 0 < p.a := by linarith [p.a_ge_one]
  have hg : 0 < 1 - p.theta := sub_pos.mpr p.theta_lt_one
  unfold eta
  exact lt_min (half_pos p.theta_pos) (lt_min (cut_pos p)
    (div_pos (mul_pos hg (cut_pos p)) (by positivity)))

theorem eta_theta (p : Parameters) : eta p ≤ p.theta / 2 := min_le_left _ _

theorem eta_cut (p : Parameters) : eta p ≤ cut p :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem eta_scaled (p : Parameters) : 2 * p.a * eta p ≤ (1 - p.theta) * cut p / 4 := by
  have ha : 0 < 4 * (2 * p.a) := by linarith [p.a_ge_one]
  have hh : eta p ≤ (1 - p.theta) * cut p / (4 * (2 * p.a)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have he := (le_div_iff₀ ha).mp hh
  nlinarith only [he]

theorem cut_identity (p : Parameters) :
    4 * p.a * cut p * ((p.k : ℝ) + 1) = p.theta * (1 - p.theta) / 2 := by
  have ha : p.a ≠ 0 := by linarith [p.a_ge_one]
  have hk : (p.k : ℝ) + 1 ≠ 0 := by positivity
  unfold cut
  field_simp
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def low (S H : Finset V) (k : ℕ) : Finset V := S.filter (fun v => hits G H v ≤ k)

/-- Count low-degree selected vertices using the density of the actual H. -/
theorem low_degree_count (a : ℝ) (hden : Incidence.InducedDensityBound G a)
    (S H : Finset V) (hSH : S ⊆ H) (k : ℕ) :
    ((k : ℝ) + 1) * S.card ≤
      ((k : ℝ) + 1) * (low G S H k).card + 2 * a * H.card := by
  let L := low G S H k
  have hLS : L ⊆ S := Finset.filter_subset _ _
  have hN : ∀ v ∈ S \ L, k + 1 ≤ hits G H v := by
    intro v hv
    obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hv
    have hh : ¬ hits G H v ≤ k := fun hh => hn (Finset.mem_filter.mpr ⟨hs, hh⟩)
    omega
  have hn : (k + 1) * (S \ L).card ≤ ∑ v ∈ H, hits G H v := by
    calc
      _ = ∑ _v ∈ S \ L, (k + 1) := by simp [mul_comm]
      _ ≤ ∑ v ∈ S \ L, hits G H v := Finset.sum_le_sum hN
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun v hv => hSH (Finset.mem_sdiff.mp hv).1) (fun _ _ _ => Nat.zero_le _)
  rw [← card_interedges G H H, Incidence.card_interedges_self] at hn
  have hr : ((k : ℝ) + 1) * (S \ L).card ≤ 2 * (G.inducedEdgeCount H : ℝ) := by
    exact_mod_cast hn
  have hc : ((S \ L).card : ℝ) + L.card = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hLS
  have hh := hden H
  change ((k : ℝ) + 1) * S.card ≤ ((k : ℝ) + 1) * L.card + 2 * a * H.card
  nlinarith only [hr, hc, hh]

/-- A low-degree vertex needs at least q-(k+1) mass outside H. -/
theorem low_light_mass (S H : Finset V) (hSH : S ⊆ H) (k : ℕ) (q : ℝ) (z : V → ℝ)
    (hz : ∀ v, 0 ≤ z v) (hcap : ∀ v, z v ≤ 1)
    (hcover : ∀ s ∈ S, q ≤ ∑ v ∈ closed G s, z v) :
    (q - ((k : ℝ) + 1)) * (low G S H k).card ≤
      ∑ s ∈ S, ∑ v ∈ G.neighborFinset s ∩ (Finset.univ \ H), z v := by
  have hpoint : ∀ s ∈ low G S H k, q - ((k : ℝ) + 1) ≤
      ∑ v ∈ G.neighborFinset s ∩ (Finset.univ \ H), z v := by
    intro s hs
    obtain ⟨hsS, hdegree⟩ := Finset.mem_filter.mp hs
    have hsH := hSH hsS
    have hf : H.filter (G.Adj s) = G.neighborFinset s ∩ H := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    have hc := Incidence.closed_inter_card G s H
    rw [hf, if_pos hsH] at hc
    have hi : (∑ v ∈ closed G s ∩ H, z v) ≤ (hits G H s : ℝ) + 1 := by
      calc
        _ ≤ ∑ _v ∈ closed G s ∩ H, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hcap v)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc, Nat.cast_add,
            Nat.cast_one]; rfl
    have he : closed G s \ (closed G s ∩ H) =
        G.neighborFinset s ∩ (Finset.univ \ H) := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and, mem_closed,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hv, hn⟩
        have hnH : v ∉ H := fun hh => hn ⟨hv, hh⟩
        rcases hv with rfl | ha
        · exact False.elim (hnH hsH)
        · exact ⟨ha, hnH⟩
      · rintro ⟨ha, hn⟩
        exact ⟨Or.inr ha, fun hh => hn hh.2⟩
    have hsplit := Finset.sum_sdiff (s₁ := closed G s ∩ H) (s₂ := closed G s)
      (f := z) Finset.inter_subset_left
    rw [he] at hsplit
    have hdeg : (hits G H s : ℝ) ≤ k := by exact_mod_cast hdegree
    linarith [hcover s hsS]
  calc
    _ = ∑ _s ∈ low G S H k, (q - ((k : ℝ) + 1)) := by simp; ring
    _ ≤ ∑ s ∈ low G S H k, ∑ v ∈ G.neighborFinset s ∩ (Finset.univ \ H), z v :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Finset.sum_nonneg (fun v _ => hz v))

/-- A uniform positive decrease of the closed-mass threshold still forces
more total weight than selected vertices. All weighted estimates are proved
from density, not supplied as an orientation or charging contract. -/
theorem mass_strict (p : Parameters) (hden : Incidence.InducedDensityBound G p.a)
    (S : Finset V) (hS : S.Nonempty) (z : V → ℝ)
    (hz : ∀ v, 0 ≤ z v) (hcap : ∀ v, z v ≤ 1)
    (hcover : ∀ s ∈ S, 2 * p.a + 1 - eta p ≤ ∑ v ∈ closed G s, z v) :
    (S.card : ℝ) < ∑ v, z v := by
  classical
  by_contra hn
  have hM : (∑ v, z v) ≤ (S.card : ℝ) := le_of_not_gt hn
  have ha : 0 ≤ p.a := by linarith [p.a_ge_one]
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have ht := cut_pos p
  let B := ∑ v ∈ (Finset.univ : Finset V) \ S, z v
  have hsplit : B + (∑ v ∈ S, z v) = ∑ v, z v :=
    Finset.sum_sdiff (Finset.subset_univ S)
  have hinc := weighted_incidence_le G p.a hden S Finset.univ z 1 (by norm_num)
    (fun v _ => hz v) (fun v _ => hcap v)
  simp only [Finset.inter_univ, mul_one] at hinc
  have hclosed : (∑ s ∈ S, ∑ v ∈ closed G s, z v) =
      (∑ s ∈ S, z s) + ∑ s ∈ S, ∑ v ∈ G.neighborFinset s, z v := by
    have hr (s : V) : (∑ v ∈ closed G s, z v) = z s + ∑ v ∈ G.neighborFinset s, z v := by
      have he : closed G s = insert s (G.neighborFinset s) := by
        ext v
        simp only [mem_closed, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      rw [he, Finset.sum_insert (by simp)]
    simp_rw [hr]
    exact Finset.sum_add_distrib
  have hcoverage : (2 * p.a + 1 - eta p) * (S.card : ℝ) ≤
      (∑ s ∈ S, z s) + p.a * (∑ v, z v) + p.a * S.card := by
    have hl := Finset.sum_le_sum hcover
    have hc : (2 * p.a + 1 - eta p) * (S.card : ℝ) ≤
        ∑ s ∈ S, ∑ v ∈ closed G s, z v := by
      simp only [Finset.sum_const, nsmul_eq_mul] at hl
      nlinarith only [hl]
    rw [hclosed] at hc
    linarith only [hc, hinc]
  have hweighted := mul_le_mul_of_nonneg_left hM ha
  have hB : B ≤ eta p * (S.card : ℝ) := by
    nlinarith only [hcoverage, hweighted, hM, hsplit]
  let T := Finset.univ.filter (fun v => v ∉ S ∧ cut p ≤ z v)
  let H := S ∪ T
  have hTS : T ⊆ (Finset.univ : Finset V) \ S := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.1⟩
  have hdis : Disjoint S T := by
    exact Finset.disjoint_left.mpr fun v hv hT => (Finset.mem_filter.mp hT).2.1 hv
  have hHcard : (H.card : ℝ) = (S.card : ℝ) + T.card := by
    exact_mod_cast Finset.card_union_of_disjoint hdis
  have hT : cut p * (T.card : ℝ) ≤ eta p * (S.card : ℝ) := by
    calc
      _ = ∑ _v ∈ T, cut p := by simp [mul_comm]
      _ ≤ ∑ v ∈ T, z v := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.2)
      _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg hTS (fun v _ _ => hz v)
      _ ≤ _ := hB
  have hlightSub : (Finset.univ : Finset V) \ H ⊆ Finset.univ \ S := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs =>
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hs)⟩
  have hlightCap : ∀ v ∈ (Finset.univ : Finset V) \ H, z v ≤ cut p := by
    intro v hv
    have hnH := (Finset.mem_sdiff.mp hv).2
    by_contra hn
    exact hnH (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp (hlightSub hv)).2, le_of_lt (lt_of_not_ge hn)⟩))
  have hlight := weighted_incidence_le G p.a hden S (Finset.univ \ H) z (cut p) ht.le
    (fun v _ => hz v) hlightCap
  have hlightMass : (∑ v ∈ (Finset.univ : Finset V) \ H, z v) ≤ B :=
    Finset.sum_le_sum_of_subset_of_nonneg hlightSub (fun v _ _ => hz v)
  have hlightWeighted := mul_le_mul_of_nonneg_left hlightMass ha
  have hBweighted := mul_le_mul_of_nonneg_left hB ha
  have hlow := low_light_mass G S H Finset.subset_union_left p.k
    (2 * p.a + 1 - eta p) z hz hcap hcover
  have hL : (p.theta - eta p) * ((low G S H p.k).card : ℝ) ≤
      p.a * (eta p + cut p) * S.card := by
    have hd := congrArg (fun q : ℝ => q * ((low G S H p.k).card : ℝ)) p.decomposition
    nlinarith only [hlow, hlight, hlightWeighted, hBweighted, hd]
  have hLcard : 0 ≤ ((low G S H p.k).card : ℝ) := Nat.cast_nonneg _
  have hLtheta := mul_le_mul_of_nonneg_right (eta_theta p) hLcard
  have hCutScaled := mul_le_mul_of_nonneg_right (eta_cut p)
    (mul_nonneg ha hs.le)
  have hLsmall : p.theta * ((low G S H p.k).card : ℝ) ≤
      4 * p.a * cut p * S.card := by nlinarith only [hL, hLtheta, hCutScaled]
  have hk : 0 ≤ (p.k : ℝ) + 1 := by positivity
  have hLscaled := mul_le_mul_of_nonneg_left hLsmall hk
  have hidentity := congrArg (fun q : ℝ => q * (S.card : ℝ)) (cut_identity p)
  have hLfinal : ((p.k : ℝ) + 1) * (low G S H p.k).card ≤
      (1 - p.theta) / 2 * S.card := by
    apply (mul_le_mul_iff_right₀ p.theta_pos).mp
    nlinarith only [hLscaled, hidentity]
  have hTscaled := mul_le_mul_of_nonneg_left hT (show 0 ≤ 2 * p.a by positivity)
  have hEtaScaled := mul_le_mul_of_nonneg_right (eta_scaled p) hs.le
  have hTfinal : 2 * p.a * T.card ≤ (1 - p.theta) / 4 * S.card := by
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith only [hTscaled, hEtaScaled]
  have hdegree := low_degree_count G p.a hden S H Finset.subset_union_left p.k
  have hHweighted := congrArg (fun q : ℝ => 2 * p.a * q) hHcard
  have hd := congrArg (fun q : ℝ => q * (S.card : ℝ)) p.decomposition
  have hgap : 0 < (1 - p.theta) * (S.card : ℝ) :=
    mul_pos (sub_pos.mpr p.theta_lt_one) hs
  nlinarith only [hdegree, hHweighted, hd, hLfinal, hTfinal, hgap]

/-- Only mass in the actual closed neighborhood of S is needed. The clipping
argument leaves every selected row unchanged. -/
theorem neighborhood_mass_gt (p : Parameters) (hden : Incidence.InducedDensityBound G p.a)
    (S : Finset V) (hS : S.Nonempty) (z : V → ℝ)
    (hz : ∀ v, 0 ≤ z v) (hcap : ∀ v, z v ≤ 1)
    (hcover : ∀ s ∈ S, 2 * p.a + 1 - eta p ≤ ∑ v ∈ closed G s, z v) :
    (S.card : ℝ) < ∑ v ∈ covered G S, z v := by
  classical
  let y := fun v => if v ∈ covered G S then z v else 0
  have hy : ∀ v, 0 ≤ y v := by
    intro v
    dsimp [y]
    split_ifs <;> first | exact hz v | exact le_rfl
  have hycap : ∀ v, y v ≤ 1 := by
    intro v
    dsimp [y]
    split_ifs <;> first | exact hcap v | exact zero_le_one
  have hycover : ∀ s ∈ S, 2 * p.a + 1 - eta p ≤ ∑ v ∈ closed G s, y v := by
    intro s hs
    have he : (∑ v ∈ closed G s, y v) = ∑ v ∈ closed G s, z v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_pos (Finset.mem_biUnion.mpr ⟨s, hs, hv⟩)
    rw [he]
    exact hcover s hs
  have hb := mass_strict G p hden S hS y hy hycap hycover
  simpa only [y, Finset.sum_ite_mem_eq] using hb

/-- The non-strict form also covers the empty selected set. -/
theorem neighborhood_mass_ge (p : Parameters) (hden : Incidence.InducedDensityBound G p.a)
    (S : Finset V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) (hcap : ∀ v, z v ≤ 1)
    (hcover : ∀ s ∈ S, 2 * p.a + 1 - eta p ≤ ∑ v ∈ closed G s, z v) :
    (S.card : ℝ) ≤ ∑ v ∈ covered G S, z v := by
  by_cases hS : S.Nonempty
  · exact (neighborhood_mass_gt G p hden S hS z hz hcap hcover).le
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [he, covered]

end Paper.Density.NeighborhoodSlack

#print axioms Paper.Density.NeighborhoodSlack.eta_pos
#print axioms Paper.Density.NeighborhoodSlack.low_degree_count
#print axioms Paper.Density.NeighborhoodSlack.low_light_mass
#print axioms Paper.Density.NeighborhoodSlack.mass_strict
#print axioms Paper.Density.NeighborhoodSlack.neighborhood_mass_ge
