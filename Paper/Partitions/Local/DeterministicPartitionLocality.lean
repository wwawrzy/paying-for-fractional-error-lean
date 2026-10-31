import Paper.Partitions.Local.DeterministicPartitionProgress
import Paper.Partitions.Local.DeterministicPartitionColors
import Paper.Preliminaries.CandidateFrameAgreement

/-! Local evaluation of the actual color sweep in a finite topology frame.
Candidate colors are compared on their actual local dependency regions;
the final theorem reconstructs them from supplied vertex colors. This
module does not compute those vertex colors or simulate graph-power rounds. -/
namespace Paper.DeterministicPartitionLocality
open DeterministicPartitionGreedy
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A q-color sweep at a candidate meeting radius r needs at most
r + q*k + k + 1 layers of topology and stage-start membership. -/
theorem run_near_color_iff (M : V → Finset V) (F S : Finset V) (x : V)
    (k t : ℕ) (color color' : Finset V → ℕ) (q : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u) :
    ∀ r : ℕ,
      NeighborBalls.ball (fun u => G.neighborFinset u) x (r + q * k + k + 1) ⊆ F →
      (∀ U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t,
        ∀ w ∈ U, w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + q * k) →
          color U = color' U) →
      ∀ (U : Finset V) (w : V), w ∈ U →
        w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r →
        (U ∈ run (FiniteEligibility.family M (F ∩ S) k t) color q ↔
          U ∈ run (FiniteEligibility.family (fun u => G.neighborFinset u) S k t) color' q) := by
  induction q with
  | zero => intro r hF hcolors U w hw hx; simp only [run, Finset.notMem_empty]
  | succ q ih =>
    intro r hF hcolors U w hw hx
    have hsmall : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + q * k + k + 1) ⊆ F :=
      (NeighborBalls.monotone _ x (by nlinarith)).trans hF
    have hbase : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k + 1) ⊆ F :=
      (NeighborBalls.monotone _ x (by nlinarith)).trans hF
    have hshift : NeighborBalls.ball (fun u => G.neighborFinset u) x
        ((r + k) + q * k + k + 1) ⊆ F := by
      have he : (r + k) + q * k + k + 1 = r + (q + 1) * k + k + 1 := by ring
      simpa only [he] using hF
    have hcolorsSmall : ∀ Z ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t,
        ∀ z ∈ Z, z ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (r + q * k) →
          color Z = color' Z := by
      intro Z hZ z hz hzb
      exact hcolors Z hZ z hz (NeighborBalls.monotone _ x (by nlinarith) hzb)
    have hcolorsShift : ∀ Z ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t,
        ∀ z ∈ Z, z ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x ((r + k) + q * k) →
          color Z = color' Z := by
      intro Z hZ z hz hzb
      have he : (r + k) + q * k = r + (q + 1) * k := by ring
      exact hcolors Z hZ z hz (by simpa only [he] using hzb)
    have hprev := ih r hsmall hcolorsSmall U w hw hx
    have hmem := CandidateFrameAgreement.near_iff G M F S U x w r k t hm hbase hw hx
    have havoid : U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t →
        ((∀ W ∈ run (FiniteEligibility.family M (F ∩ S) k t) color q, Disjoint U W) ↔
          (∀ W ∈ run (FiniteEligibility.family (fun u => G.neighborFinset u) S k t) color' q,
            Disjoint U W)) := by
      intro hu
      have hh := (FiniteEligibility.mem_family _ S U k t).mp hu
      have hc := (FiniteConnectivity.correct G U).mp hh.2.1
      have hUball := CandidateGeometry.connected_subset_ball G U hc k hh.2.2.1 w hw x r hx
      constructor
      · intro ha W hW
        by_cases hd : Disjoint U W
        · exact hd
        · obtain ⟨v, hvU, hvW⟩ := Finset.not_disjoint_iff.mp hd
          exact ha W ((ih (r + k) hshift hcolorsShift W v hvW (hUball hvU)).mpr hW)
      · intro ha W hW
        by_cases hd : Disjoint U W
        · exact hd
        · obtain ⟨v, hvU, hvW⟩ := Finset.not_disjoint_iff.mp hd
          exact ha W ((ih (r + k) hshift hcolorsShift W v hvW (hUball hvU)).mp hW)
    simp only [run, Finset.mem_union]
    constructor
    · rintro (hu | hu)
      · exact Or.inl (hprev.mp hu)
      · have hh := (mem_batch _ color _ q U).mp hu
        have he := hmem.mp hh.1
        have hcol := hcolors U he w hw (NeighborBalls.monotone _ x (by nlinarith) hx)
        exact Or.inr ((mem_batch _ color' _ q U).mpr
          ⟨he, hcol.symm.trans hh.2.1, (havoid he).mp hh.2.2⟩)
    · rintro (hu | hu)
      · exact Or.inl (hprev.mpr hu)
      · have hh := (mem_batch _ color' _ q U).mp hu
        have hcol := hcolors U hh.1 w hw (NeighborBalls.monotone _ x (by nlinarith) hx)
        exact Or.inr ((mem_batch _ color _ q U).mpr
          ⟨hmem.mpr hh.1, hcol.trans hh.2.1, (havoid hh.1).mpr hh.2.2⟩)

theorem run_near_iff (M : V → Finset V) (F S : Finset V) (x : V)
    (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (r : ℕ) (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + q * k + k + 1) ⊆ F)
    (U : Finset V) (w : V) (hw : w ∈ U)
    (hx : w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x r) :
    U ∈ run (FiniteEligibility.family M (F ∩ S) k t) color q ↔
      U ∈ run (FiniteEligibility.family (fun u => G.neighborFinset u) S k t) color q :=
  run_near_color_iff G M F S x k t color color q hm r hF
    (fun _ _ _ _ _ => rfl) U w hw hx

/-- Complete candidate sets accepted at x, using only a finite frame. -/
def atVertex (E : Finset (Finset V)) (color : Finset V → ℕ) (q : ℕ) (x : V) :
    Finset (Finset V) :=
  (run E color q).filter (fun U => x ∈ U)

def part (E : Finset (Finset V)) (color : Finset V → ℕ) (q : ℕ) (x : V) : Finset V :=
  (atVertex E color q x).biUnion id

theorem part_of_mem (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hc : Proper E color) (q : ℕ) (x : V) (U : Finset V)
    (hU : U ∈ run E color q) (hx : x ∈ U) : part E color q x = U := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨W, hW, hvW⟩ := Finset.mem_biUnion.mp hv
    have hw := Finset.mem_filter.mp hW
    have he : W = U := by
      by_contra hn
      exact Finset.disjoint_left.mp (disjoint E color hc q hw.1 hU hn) hw.2 hx
    simpa only [he] using hvW
  · intro v hv
    exact Finset.mem_biUnion.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hx⟩, hv⟩

theorem atVertex_eq (M : V → Finset V) (F S : Finset V) (x : V)
    (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (q * k + k + 1) ⊆ F) :
    atVertex (FiniteEligibility.family M (F ∩ S) k t) color q x =
      atVertex (FiniteEligibility.family (fun u => G.neighborFinset u) S k t) color q x := by
  ext U
  simp only [atVertex, Finset.mem_filter]
  by_cases hx : x ∈ U
  · have hh := run_near_iff G M F S x k t color q hm 0
      (by simpa only [Nat.zero_add] using hF) U x hx (NeighborBalls.self_mem _ x 0)
    exact and_congr hh Iff.rfl
  · simp only [hx, and_false]

theorem part_eq (M : V → Finset V) (F S : Finset V) (x : V)
    (k t : ℕ) (color : Finset V → ℕ) (q : ℕ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (q * k + k + 1) ⊆ F) :
    part (FiniteEligibility.family M (F ∩ S) k t) color q x =
      part (FiniteEligibility.family (fun u => G.neighborFinset u) S k t) color q x := by
  unfold part
  rw [atVertex_eq G M F S x k t color q hm hF]

/-- The local execution computes its candidate colors from the local
frame and the supplied vertex colors; no global candidate-color oracle. -/
theorem colored_part_eq (M : V → Finset V) (F S : Finset V) (x : V)
    (Δ k t : ℕ) (fallback : V) (Φ : ℕ) (χ : V → Fin Φ)
    (q : ℕ) (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (q * k + 2 * k + 1) ⊆ F) :
    part (FiniteEligibility.family M (F ∩ S) k t)
        (DeterministicPartitionColors.color M Δ k fallback Φ χ) q x =
      part (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ) q x := by
  have hsmall : NeighborBalls.ball (fun u => G.neighborFinset u) x (0 + q * k + k + 1) ⊆ F :=
    (NeighborBalls.monotone _ x (by omega)).trans hF
  have hcolors : ∀ U ∈ FiniteEligibility.family (fun u => G.neighborFinset u) S k t,
      ∀ w ∈ U, w ∈ NeighborBalls.ball (fun u => G.neighborFinset u) x (0 + q * k) →
        DeterministicPartitionColors.color M Δ k fallback Φ χ U =
          DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ U := by
    intro U hU w hw hx
    have hh := (FiniteEligibility.mem_family _ S U k t).mp hU
    have hc := (FiniteConnectivity.correct G U).mp hh.2.1
    have hUb := CandidateGeometry.connected_subset_ball G U hc k hh.2.2.1 w hw x
      (q * k) (by simpa only [Nat.zero_add] using hx)
    apply DeterministicPartitionColors.color_eq G M F U x (q * k + k) Δ k fallback Φ χ hm
    · exact (NeighborBalls.monotone _ x (by omega)).trans hF
    · exact hUb
    · exact ⟨w, hw⟩
  have hat : atVertex (FiniteEligibility.family M (F ∩ S) k t)
        (DeterministicPartitionColors.color M Δ k fallback Φ χ) q x =
      atVertex (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ) q x := by
    ext U
    simp only [atVertex, Finset.mem_filter]
    by_cases hx : x ∈ U
    · have hh := run_near_color_iff G M F S x k t
        (DeterministicPartitionColors.color M Δ k fallback Φ χ)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ)
        q hm 0 hsmall hcolors U x hx (NeighborBalls.self_mem _ x 0)
      exact and_congr hh Iff.rfl
    · simp only [hx, and_false]
  exact congrArg (fun A : Finset (Finset V) => A.biUnion id) hat

end Paper.DeterministicPartitionLocality

#print axioms Paper.DeterministicPartitionLocality.run_near_iff
#print axioms Paper.DeterministicPartitionLocality.part_eq

#print axioms Paper.DeterministicPartitionLocality.colored_part_eq
