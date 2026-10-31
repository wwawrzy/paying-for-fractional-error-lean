import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry
import Paper.Preliminaries.ShortChains
import Paper.Partitions.Local.BoundedBallBridge
import Paper.Averaging.Tasks.ActiveTaskContext

/-! Physical connectivity and 4k walks for the exact arbitrary-C task region.
Owner interactions are lifted through their actual light admissible witness
and two accepted owner-star representatives. Every intermediate vertex lies
in TaskGeometry.vertices. This is analysis geometry, not runtime partitioning. -/
namespace Paper.GeneralCoveringTaskDiameter
open SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def physicalGraph (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) : SimpleGraph ↥(vertices G C D R L Q I : Set V) :=
  G.induce (vertices G C D R L Q I : Set V)

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

local instance physicalAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) : DecidableRel (physicalGraph G C D R L Q I).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u.val v.val))

theorem empty_part (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    vertices G C D R L Q ∅ = ∅ ∧ ∀ Bdy, demands G C D R L Q ∅ Bdy = ∅ := by
  constructor
  · simp [vertices]
  · intro Bdy
    ext r
    simp [demands]

/-- Nonempty physical region is equivalent to nonempty owner part, with no
assertion that this part has any residual demands. -/
theorem vertices_nonempty_iff (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) : (vertices G C D R L Q I).Nonempty ↔ I.Nonempty := by
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hs | hc
    · obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp hs
      exact ⟨i, hi⟩
    · obtain ⟨i, hi, _⟩ := (Finset.mem_filter.mp hc).2
      exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val.val, owner_in_vertices G C D R L Q I hi⟩

noncomputable def root (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (i : ↥(I : Set (Low D Q))) : ↥(vertices G C D R L Q I : Set V) :=
  ⟨i.val.val.val, owner_in_vertices G C D R L Q I i.property⟩

theorem star_mem (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) {i : Low D Q} (hi : i ∈ I) {v : V}
    (ho : GeneralCoveringOwners.owner C D R v = some i.val.val) : v ∈ vertices G C D R L Q I :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi,
    Finset.mem_filter.mpr ⟨GeneralCoveringOwners.owner_domain C D R ho, ho⟩⟩)

theorem witness_mem (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) {i : Low D Q} (hi : i ∈ I) {v : V}
    (hv : i.val.val ∈ lightSupport G C D R L v) : v ∈ vertices G C D R L Q I :=
  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hv⟩)

theorem interaction_witness (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) {i j : ↥(I : Set (Low D Q))}
    (ha : ((graph G C D R L Q).induce (I : Set (Low D Q))).Adj i j) :
    ∃ m ∈ vertices G C D R L Q I, m ∈ CoveringSupport.admissible C R ∧
      m ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
      i.val.val.val ∈ GeneralCoveringOwnerSupport.support G C D R m ∧
      j.val.val.val ∈ GeneralCoveringOwnerSupport.support G C D R m := by
  obtain ⟨_, m, hmi, hmj⟩ := ha
  have hi := (mem_lightSupport G C D R L m i.val.val.val).mp hmi
  have hj := (mem_lightSupport G C D R L m j.val.val.val).mp hmj
  exact ⟨m, witness_mem G C D R L Q I i.property hmi, hi.1, hi.2.1, hi.2.2, hj.2.2⟩

/-- Each owner edge lifts to an actual four-step physical chain inside H. -/
theorem edge_route (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {i j : ↥(I : Set (Low D Q))}
    (ha : ((graph G C D R L Q).induce (I : Set (Low D Q))).Adj i j) :
    ∃ p : (physicalGraph G C D R L Q I).Walk (root G C D R L Q I i) (root G C D R L Q I j),
      p.length ≤ 4 := by
  let H := vertices G C D R L Q I
  obtain ⟨m, hmH, _, _, hmi, hmj⟩ := interaction_witness G C D R L Q I ha
  obtain ⟨r, hr, hri⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R m i.val.val.val).mp hmi
  obtain ⟨s, hs, hsj⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R m j.val.val.val).mp hmj
  have hiH : i.val.val.val ∈ H := owner_in_vertices G C D R L Q I i.property
  have hjH : j.val.val.val ∈ H := owner_in_vertices G C D R L Q I j.property
  have hrH : r ∈ H := star_mem G C D R L Q I i.property hri
  have hsH : s ∈ H := star_mem G C D R L Q I j.property hsj
  have h₀ := GeneralCoveringOwners.owner_star G C D R hlocal hri
  have h₁ : r = m ∨ G.Adj r m :=
    ((mem_closed G r m).mp hr).elim Or.inl (fun h => Or.inr h.symm)
  have h₂ : m = s ∨ G.Adj m s :=
    ((mem_closed G s m).mp hs).elim (fun h => Or.inl h.symm) Or.inr
  have h₃ : s = j.val.val.val ∨ G.Adj s j.val.val.val :=
    (GeneralCoveringOwners.owner_star G C D R hlocal hsj).elim
      (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  obtain ⟨p, hp, hps⟩ := ShortChains.chain5 G i.val.val.val r m s j.val.val.val h₀ h₁ h₂ h₃
  have hset : ({i.val.val.val, r, m, s, j.val.val.val} : Finset V) ⊆ H := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hiH, hrH, hmH, hsH, hjH⟩
  have hpH : ∀ z ∈ p.support, z ∈ H := fun z hz => hset (hps z hz)
  refine ⟨p.induce (H : Set V) hpH, ?_⟩
  exact (ShortChains.induce_length G H p hpH).trans_le hp

theorem near_root (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (x : ↥(vertices G C D R L Q I : Set V)) :
    ∃ i : ↥(I : Set (Low D Q)), ∃ p : (physicalGraph G C D R L Q I).Walk x (root G C D R L Q I i),
      p.length ≤ 2 := by
  let H := vertices G C D R L Q I
  rcases Finset.mem_union.mp x.property with hstar | hcandidate
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hstar
    have ho := (Finset.mem_filter.mp hxi).2
    let j : ↥(I : Set (Low D Q)) := ⟨i, hi⟩
    have hiH : i.val.val ∈ H := owner_in_vertices G C D R L Q I hi
    have hstep : x.val = i.val.val ∨ G.Adj x.val i.val.val :=
      (GeneralCoveringOwners.owner_star G C D R hlocal ho).elim
        (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    obtain ⟨p, hp, hps⟩ := ShortChains.step G hstep
    have hpH : ∀ z ∈ p.support, z ∈ H := by
      intro z hz
      rcases hps z hz with he | he
      · simpa only [he] using x.property
      · simpa only [he] using hiH
    refine ⟨j, p.induce (H : Set V) hpH, ?_⟩
    exact (ShortChains.induce_length G H p hpH).trans_le (hp.trans (by omega))
  · obtain ⟨i, hi, hil⟩ := (Finset.mem_filter.mp hcandidate).2
    have his := ((mem_lightSupport G C D R L x.val i.val.val).mp hil).2.2
    obtain ⟨r, hr, hri⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R x.val i.val.val).mp his
    let j : ↥(I : Set (Low D Q)) := ⟨i, hi⟩
    have hiH : i.val.val ∈ H := owner_in_vertices G C D R L Q I hi
    have hrH : r ∈ H := star_mem G C D R L Q I hi hri
    have h₀ : x.val = r ∨ G.Adj x.val r :=
      ((mem_closed G r x.val).mp hr).elim (fun h => Or.inl h.symm) Or.inr
    have h₁ : r = i.val.val ∨ G.Adj r i.val.val :=
      (GeneralCoveringOwners.owner_star G C D R hlocal hri).elim
        (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    obtain ⟨p, hp, hps⟩ := ShortChains.chain3 G x.val r i.val.val h₀ h₁
    have hset : ({x.val, r, i.val.val} : Finset V) ⊆ H := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨x.property, hrH, hiH⟩
    have hpH : ∀ z ∈ p.support, z ∈ H := fun z hz => hset (hps z hz)
    refine ⟨j, p.induce (H : Set V) hpH, ?_⟩
    exact (ShortChains.induce_length G H p hpH).trans_le hp

theorem roots (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (i j : ↥(I : Set (Low D Q))) :
    ∃ p : (physicalGraph G C D R L Q I).Walk (root G C D R L Q I i) (root G C D R L Q I j),
      p.length ≤ 4 * (I.card - 1) := by
  obtain ⟨p, hp⟩ := (hI i j).exists_isPath
  have hlen : p.length < I.card := by
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hp.length_lt
  obtain ⟨q, hq⟩ := ShortChains.lift_walk (physicalGraph G C D R L Q I)
    ((graph G C D R L Q).induce (I : Set (Low D Q))) (root G C D R L Q I) 4
    (fun h => edge_route G C D R L Q I hlocal h) p
  exact ⟨q, hq.trans (Nat.mul_le_mul_left 4 (by omega))⟩

/-- The constants are 2 + 4*(|I|-1) + 2 = 4*|I| <= 4*k. -/
theorem walk_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (x y : ↥(vertices G C D R L Q I : Set V)) :
    ∃ p : (physicalGraph G C D R L Q I).Walk x y, p.length ≤ 4 * k := by
  obtain ⟨i, px, hx⟩ := near_root G C D R L Q I hlocal x
  obtain ⟨j, py, hy⟩ := near_root G C D R L Q I hlocal y
  obtain ⟨q, hq⟩ := roots G C D R L Q I hlocal hI i j
  have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i.val, i.property⟩
  refine ⟨px.append (q.append py.reverse), ?_⟩
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

theorem spec (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    (physicalGraph G C D R L Q I).Connected ∧
      ∀ x y, ∃ p : (physicalGraph G C D R L Q I).Walk x y, p.length ≤ 4 * k := by
  have hwalk := walk_bound G C D R L Q I hlocal hI k hsize
  obtain ⟨i⟩ := hI.nonempty
  letI : Nonempty ↥(vertices G C D R L Q I : Set V) := ⟨root G C D R L Q I i⟩
  exact ⟨⟨fun x y => ⟨(hwalk x y).choose⟩⟩, hwalk⟩

theorem distance_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (x y : ↥(vertices G C D R L Q I : Set V)) :
    (physicalGraph G C D R L Q I).dist x y ≤ 4 * k := by
  obtain ⟨p, hp⟩ := walk_bound G C D R L Q I hlocal hI k hsize x y
  exact (SimpleGraph.dist_le p).trans hp

theorem neighbor_ball_cover (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (x y : ↥(vertices G C D R L Q I : Set V)) :
    y ∈ NeighborBalls.ball (fun u => (physicalGraph G C D R L Q I).neighborFinset u) x (4 * k) := by
  obtain ⟨p, hp⟩ := walk_bound G C D R L Q I hlocal hI k hsize x y
  exact NeighborBallGraph.walk_mem _ p (4 * k) hp

theorem bounded_ball_cover (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (x y : ↥(vertices G C D R L Q I : Set V)) :
    y ∈ BoundedBall.ball (physicalGraph G C D R L Q I) x (4 * k) := by
  obtain ⟨p, hp⟩ := walk_bound G C D R L Q I hlocal hI k hsize x y
  have hmem : y ∈ BoundedBall.ball (physicalGraph G C D R L Q I) x p.length :=
    BoundedBall.walk_mem (physicalGraph G C D R L Q I) p
  exact BoundedBall.mono (physicalGraph G C D R L Q I) x hp hmem

/-- Physical task context with paths derived above, never supplied as an
extra distance/connectivity oracle. Nonempty demands are not required. -/
noncomputable def context (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) : ActiveTask.Context G where
  vertices := vertices G C D R L Q I
  nonempty := by
    obtain ⟨i⟩ := hI.nonempty
    exact ⟨i.val.val.val, (root G C D R L Q I i).property⟩
  diameter := 4 * k
  paths := walk_bound G C D R L Q I hlocal hI k hsize

theorem context_root_mem (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    (vertices G C D R L Q I).min' (context G C D R L Q I hlocal hI k hsize).nonempty ∈
      vertices G C D R L Q I := Finset.min'_mem _ _

noncomputable def maskedContext (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    ActiveTask.Context (MaskedTaskGraph.graph G (vertices G C D R L Q I)) where
  vertices := vertices G C D R L Q I
  nonempty := (context G C D R L Q I hlocal hI k hsize).nonempty
  diameter := 4 * k
  paths := by
    intro x y
    rw [MaskedTaskGraph.induced_eq G]
    exact walk_bound G C D R L Q I hlocal hI k hsize x y

/-- Existing finite partition data supply owner connectivity and size.
This constructor is proof-side and makes no executable-partition claim. -/
noncomputable def partContext (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (I : Finset (Low D Q)) (hI : I ∈ P.parts) : ActiveTask.Context G :=
  context G C D R L Q I hlocal (P.connected I hI) k (P.size I hI)

end Paper.GeneralCoveringTaskDiameter

#print axioms Paper.GeneralCoveringTaskDiameter.empty_part
#print axioms Paper.GeneralCoveringTaskDiameter.vertices_nonempty_iff
#print axioms Paper.GeneralCoveringTaskDiameter.interaction_witness
#print axioms Paper.GeneralCoveringTaskDiameter.edge_route
#print axioms Paper.GeneralCoveringTaskDiameter.near_root
#print axioms Paper.GeneralCoveringTaskDiameter.roots
#print axioms Paper.GeneralCoveringTaskDiameter.walk_bound
#print axioms Paper.GeneralCoveringTaskDiameter.spec
#print axioms Paper.GeneralCoveringTaskDiameter.distance_bound
#print axioms Paper.GeneralCoveringTaskDiameter.neighbor_ball_cover
#print axioms Paper.GeneralCoveringTaskDiameter.bounded_ball_cover
#print axioms Paper.GeneralCoveringTaskDiameter.context
#print axioms Paper.GeneralCoveringTaskDiameter.context_root_mem
#print axioms Paper.GeneralCoveringTaskDiameter.maskedContext
#print axioms Paper.GeneralCoveringTaskDiameter.partContext
