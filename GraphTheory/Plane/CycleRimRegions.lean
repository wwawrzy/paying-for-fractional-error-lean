import GraphTheory.Plane.PlanarMaximalStructure

/-!
# Actual walk intervals realize Wagner's rim-region obstructions

The sets used below are images of explicit half-open intervals of positions in
an actual simple cycle. The final region wraps through the cycle's starting
vertex. Connectedness, disjointness and neighboring all follow from the walk;
they are not external region assumptions.
-/

namespace PlaneTopology.CycleRimRegions

open SimpleGraph PlaneTopology.PlanarMaximalStructure

variable {V : Type*} {G : SimpleGraph V} {u v z : V}

/-- The vertices at a specified set of positions of an actual walk. -/
def region (p : G.Walk u v) (s : Set ℕ) : Set V := p.getVert '' s

/-- Every nonempty half-open interval of walk positions induces a connected graph. -/
theorem connected_region_Ico (p : G.Walk u v) {a b : ℕ}
    (hab : a < b) (hbn : b ≤ p.length + 1) :
    (G.induce (region p (Set.Ico a b))).Connected := by
  let base : region p (Set.Ico a b) := ⟨p.getVert a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩
  have hreach : ∀ (k) (hak : a ≤ k), ∀ hkb : k < b,
      (G.induce (region p (Set.Ico a b))).Reachable base
        ⟨p.getVert k, ⟨k, ⟨hak, hkb⟩, rfl⟩⟩ := by
    intro k hak
    induction k, hak using Nat.le_induction with
    | base =>
      intro hkb
      exact Reachable.refl _
    | succ k hak ih =>
      intro hkb
      have hk : k < b := by omega
      exact (ih hk).trans (Adj.reachable (p.adj_getVert_succ (by omega)))
  rw [connected_iff_exists_forall_reachable]
  refine ⟨base, ?_⟩
  intro ⟨w, hw⟩
  obtain ⟨k, ⟨hak, hkb⟩, rfl⟩ := hw
  exact hreach k hak hkb

/-- The final wrapped interval of a cycle is connected. -/
theorem connected_region_wrap (p : G.Walk z z) {a b : ℕ}
    (hab : a ≤ b) (hbn : b < p.length) :
    (G.induce (region p (Set.Ico b p.length ∪ Set.Ico 0 a))).Connected := by
  by_cases ha : a = 0
  · subst a
    change (G.induce (p.getVert '' (Set.Ico b p.length ∪ Set.Ico 0 0))).Connected
    rw [Set.Ico_self, Set.union_empty]
    exact connected_region_Ico p hbn (by omega)
  · have hbconn := connected_region_Ico p hbn (by omega)
    have haconn := connected_region_Ico p (show 0 < a by omega) (by omega)
    have hbmem : p.getVert (p.length - 1) ∈ region p (Set.Ico b p.length) :=
      ⟨p.length - 1, ⟨by omega, by omega⟩, rfl⟩
    have hamem : p.getVert 0 ∈ region p (Set.Ico 0 a) :=
      ⟨0, ⟨le_rfl, by omega⟩, rfl⟩
    have hclose : G.Adj (p.getVert (p.length - 1)) (p.getVert 0) := by
      have h := p.adj_getVert_succ (i := p.length - 1) (by omega)
      simpa only [show p.length - 1 + 1 = p.length by omega,
        Walk.getVert_length, Walk.getVert_zero] using h
    change (G.induce (p.getVert '' (Set.Ico b p.length ∪ Set.Ico 0 a))).Connected
    rw [Set.image_union]
    exact connected_induce_union hbconn.preconnected haconn.preconnected hbmem hamem hclose

/-- Disjoint position sets below the cycle length have disjoint vertex images. -/
theorem disjoint_regions (p : G.Walk z z) (hp : p.IsCycle)
    {s t : Set ℕ} (hs : s ⊆ Set.Iio p.length) (ht : t ⊆ Set.Iio p.length)
    (hst : Disjoint s t) : Disjoint (region p s) (region p t) := by
  rw [Set.disjoint_left] at hst ⊢
  rintro w ⟨i, hi, hwi⟩ ⟨j, hj, hwj⟩
  have hij : i = j := hp.getVert_injOn' (by have := hs hi; simp at *; omega)
    (by have := ht hj; simp at *; omega) (hwi.trans hwj.symm)
  subst j
  exact hst hi hj

/-- A vertex outside a walk is outside every region cut from the walk. -/
theorem not_mem_region_of_not_mem_support (p : G.Walk u v) {x : V}
    (hx : x ∉ p.support) (s : Set ℕ) : x ∉ region p s := by
  rintro ⟨i, _, rfl⟩
  exact hx (p.getVert_mem_support i)

/-- Consecutive walk positions join their respective vertex regions. -/
theorem neighboring_regions_of_step (p : G.Walk u v) {s t : Set ℕ} {i : ℕ}
    (hi : i < p.length) (his : i ∈ s) (hit : i + 1 ∈ t) :
    Neighboring G (region p s) (region p t) :=
  ⟨p.getVert i, ⟨i, his, rfl⟩, p.getVert (i + 1), ⟨i + 1, hit, rfl⟩,
    p.adj_getVert_succ hi⟩

/-- The last-to-first edge of a cycle joins its respective regions. -/
theorem neighboring_regions_of_close (p : G.Walk z z) {s t : Set ℕ}
    (hn : 0 < p.length) (hs : p.length - 1 ∈ s) (ht : 0 ∈ t) :
    Neighboring G (region p s) (region p t) := by
  refine ⟨p.getVert (p.length - 1), ⟨_, hs, rfl⟩,
    p.getVert 0, ⟨0, ht, rfl⟩, ?_⟩
  have h := p.adj_getVert_succ (i := p.length - 1) (by omega)
  simpa only [show p.length - 1 + 1 = p.length by omega,
    Walk.getVert_length, Walk.getVert_zero] using h

/-- The wrap region is joined to the interval beginning at its endpoint. -/
theorem neighboring_wrap_Ico (p : G.Walk z z) {a b c : ℕ}
    (hab : a < b) (hbc : b ≤ c) (hcn : c < p.length) :
    Neighboring G (region p (Set.Ico c p.length ∪ Set.Ico 0 a))
      (region p (Set.Ico a b)) := by
  by_cases ha : a = 0
  · subst a
    exact neighboring_regions_of_close p (by omega)
      (Or.inl ⟨by omega, by omega⟩) ⟨le_rfl, hab⟩
  · apply neighboring_regions_of_step p (i := a - 1) (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

/-- Three common neighbors in cyclic order yield an actual K₅ minor. -/
theorem k5_minor_of_ordered_cycle_neighbors (p : G.Walk z z) (hp : p.IsCycle)
    (x y : V) (hxy : G.Adj x y) (hx : x ∉ p.support) (hy : y ∉ p.support)
    (a b c : ℕ) (hab : a < b) (hbc : b < c) (hcn : c < p.length)
    (hxa : G.Adj x (p.getVert a)) (hxb : G.Adj x (p.getVert b))
    (hxc : G.Adj x (p.getVert c)) (hya : G.Adj y (p.getVert a))
    (hyb : G.Adj y (p.getVert b)) (hyc : G.Adj y (p.getVert c)) :
    (completeGraph (Fin 5)).IsMinor G := by
  let S : Fin 3 → Set ℕ :=
    ![Set.Ico a b, Set.Ico b c, Set.Ico c p.length ∪ Set.Ico 0 a]
  let A : Fin 3 → Set V := fun i => region p (S i)
  have hsub : ∀ i, S i ⊆ Set.Iio p.length := by
    intro i k hk
    fin_cases i <;> dsimp [S] at hk <;>
      simp only [Set.mem_Ico, Set.mem_union] at hk <;>
      change k < p.length <;> omega
  have hconn : ∀ i, (G.induce (A i)).Connected := by
    intro i
    fin_cases i
    · exact connected_region_Ico p hab (by omega)
    · exact connected_region_Ico p hbc (by omega)
    · exact connected_region_wrap p (by omega) hcn
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply disjoint_regions p hp (hsub i) (hsub j)
    rw [Set.disjoint_left]
    intro k hki hkj
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | skip
    all_goals dsimp [S] at hki hkj
    all_goals simp only [Set.mem_Ico, Set.mem_union] at hki hkj
    all_goals omega
  have hn01 : Neighboring G (A 0) (A 1) := by
    apply neighboring_regions_of_step p (i := b - 1) (by omega)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hn12 : Neighboring G (A 1) (A 2) := by
    apply neighboring_regions_of_step p (i := c - 1) (by omega)
    · exact ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  have hn20 : Neighboring G (A 2) (A 0) :=
    neighboring_wrap_Ico p hab (by omega) hcn
  apply k5_minor_of_three_regions x y A hxy hconn hdisj
  · exact fun i => not_mem_region_of_not_mem_support p hx (S i)
  · exact fun i => not_mem_region_of_not_mem_support p hy (S i)
  · intro i
    rw [neighboring_singleton_left]
    fin_cases i
    · exact ⟨p.getVert a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, hxa⟩
    · exact ⟨p.getVert b, ⟨b, ⟨le_rfl, hbc⟩, rfl⟩, hxb⟩
    · exact ⟨p.getVert c, ⟨c, Or.inl ⟨le_rfl, hcn⟩, rfl⟩, hxc⟩
  · intro i
    rw [neighboring_singleton_left]
    fin_cases i
    · exact ⟨p.getVert a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, hya⟩
    · exact ⟨p.getVert b, ⟨b, ⟨le_rfl, hbc⟩, rfl⟩, hyb⟩
    · exact ⟨p.getVert c, ⟨c, Or.inl ⟨le_rfl, hcn⟩, rfl⟩, hyc⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hn01 | exact hn01.symm | exact hn12 | exact hn12.symm
      | exact hn20 | exact hn20.symm

/-- Four alternating attachments in cyclic order yield an actual K₃,₃ minor. -/
theorem k33_minor_of_ordered_cycle_neighbors (p : G.Walk z z) (hp : p.IsCycle)
    (x y : V) (hxy : G.Adj x y) (hx : x ∉ p.support) (hy : y ∉ p.support)
    (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hdn : d < p.length)
    (hxa : G.Adj x (p.getVert a)) (hxc : G.Adj x (p.getVert c))
    (hyb : G.Adj y (p.getVert b)) (hyd : G.Adj y (p.getVert d)) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).IsMinor G := by
  let S : Fin 4 → Set ℕ := ![Set.Ico a b, Set.Ico b c, Set.Ico c d,
    Set.Ico d p.length ∪ Set.Ico 0 a]
  let A : Fin 4 → Set V := fun i => region p (S i)
  have hsub : ∀ i, S i ⊆ Set.Iio p.length := by
    intro i k hk
    fin_cases i <;> dsimp [S] at hk <;>
      simp only [Set.mem_Ico, Set.mem_union] at hk <;>
      change k < p.length <;> omega
  have hconn : ∀ i, (G.induce (A i)).Connected := by
    intro i
    fin_cases i
    · exact connected_region_Ico p hab (by omega)
    · exact connected_region_Ico p hbc (by omega)
    · exact connected_region_Ico p hcd (by omega)
    · exact connected_region_wrap p (by omega) hdn
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply disjoint_regions p hp (hsub i) (hsub j)
    rw [Set.disjoint_left]
    intro k hki hkj
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | skip
    all_goals dsimp [S] at hki hkj
    all_goals simp only [Set.mem_Ico, Set.mem_union] at hki hkj
    all_goals omega
  have hn01 : Neighboring G (A 0) (A 1) := by
    apply neighboring_regions_of_step p (i := b - 1) (by omega)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hn12 : Neighboring G (A 1) (A 2) := by
    apply neighboring_regions_of_step p (i := c - 1) (by omega)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hn23 : Neighboring G (A 2) (A 3) := by
    apply neighboring_regions_of_step p (i := d - 1) (by omega)
    · exact ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  have hn30 : Neighboring G (A 3) (A 0) :=
    neighboring_wrap_Ico p hab (by omega) hdn
  apply k33_minor_of_alternating_regions x y A hxy hconn hdisj
  · exact fun i => not_mem_region_of_not_mem_support p hx (S i)
  · exact fun i => not_mem_region_of_not_mem_support p hy (S i)
  · rw [neighboring_singleton_left]
    exact ⟨p.getVert a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, hxa⟩
  · rw [neighboring_singleton_left]
    exact ⟨p.getVert c, ⟨c, ⟨le_rfl, hcd⟩, rfl⟩, hxc⟩
  · rw [neighboring_singleton_left]
    exact ⟨p.getVert b, ⟨b, ⟨le_rfl, hbc⟩, rfl⟩, hyb⟩
  · rw [neighboring_singleton_left]
    exact ⟨p.getVert d, ⟨d, Or.inl ⟨le_rfl, hdn⟩, rfl⟩, hyd⟩
  · intro i
    fin_cases i
    · exact hn01
    · exact hn12
    · exact hn23
    · exact hn30

end PlaneTopology.CycleRimRegions

#print axioms PlaneTopology.CycleRimRegions.k5_minor_of_ordered_cycle_neighbors
#print axioms PlaneTopology.CycleRimRegions.k33_minor_of_ordered_cycle_neighbors
