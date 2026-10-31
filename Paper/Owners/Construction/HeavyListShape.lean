import Paper.Owners.Construction.HeavyListing

/-! The heavy-list program always returns one common bounded initialList,
including when the large-demand precondition is false. This total shape
is needed to pad the recursive search into a fixed broadcast schedule. -/
namespace Paper.HeavyListShape
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def initialList (H A : Finset V) (a m : ℕ) : List V :=
  MinimumList.run (H ∩ LocalSearchBounds.heavy G A m) (2 * a * m)

theorem length (H A : Finset V) (a m : ℕ) : (initialList G H A a m).length ≤ 2 * a * m :=
  MinimumList.run_length _ _

theorem subset (H A : Finset V) (a m : ℕ) {u : V} (hu : u ∈ initialList G H A a m) :
    u ∈ H ∧ u ∈ LocalSearchBounds.heavy G A m :=
  Finset.mem_inter.mp (MinimumList.run_subset _ _ (List.mem_toFinset.mpr hu))

theorem complete (H A : Finset V) (a m : ℕ) (ha : 1 ≤ a) (hm : 1 ≤ m)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (hlarge : 2 * (a + 1) * m ≤ A.card) :
    (initialList G H A a m).toFinset = H ∩ LocalSearchBounds.heavy G A m := by
  apply MinimumList.complete
  have hheavy : (LocalSearchBounds.heavy G A m).card ≤ 2 * a * m := by
    exact_mod_cast LocalSearchBounds.heavy_card_le G A m hm
      (by exact_mod_cast ha : (1 : ℝ) ≤ a) hden (by exact_mod_cast hlarge)
  exact (Finset.card_le_card (Finset.inter_subset_right :
    H ∩ LocalSearchBounds.heavy G A m ⊆ LocalSearchBounds.heavy G A m)).trans hheavy

theorem chosen {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (A : Finset V)
    (hA : A ⊆ PhysicalTasks.vertices G D R L Q I) (a m : ℕ) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((HeavyListing.program C (4 * k) a m).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) v).chosen =
          initialList G (PhysicalTasks.vertices G D R L Q I) A a m := by
  let H := PhysicalTasks.vertices G D R L Q I
  let active : V → Bool := fun v => decide (v ∈ H)
  let input : V → Bool × Bool := fun v => (active v, decide (v ∈ A))
  let E : V → Bool := fun v => ((HeavyEligibility.program C (4 * k) m).run G input v).2
  have hE (v : V) (hv : v ∈ H) : E v =
      decide (A.card ≤ m * (SevenFoundation.closed G v ∩ A).card) :=
    HeavyEligibility.physical_task G C D R L Q I hI k hsize A hA m v hv
  have he : SelectStep.candidates active E = H ∩ LocalSearchBounds.heavy G A m := by
    ext v
    by_cases hv : v ∈ H
    · simp [SelectStep.candidates, active, hv, hE v hv, LocalSearchBounds.heavy]
    · simp [SelectStep.candidates, active, hv]
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  have har : active (H.min' hne) = true := decide_eq_true (Finset.min'_mem _ hne)
  have hi : (HeavyEligibility.program C (4 * k) m).run G input = fun v => (active v, E v) := by
    funext v
    exact Prod.ext (HeavyEligibility.active G C (4 * k) m input v) rfl
  have hrun : (HeavyListing.program C (4 * k) a m).run G input =
      (SelectProtocol.program C (4 * k) (2 * a * m)).run G (fun v => (active v, E v)) := by
    change (SelectProtocol.program C (4 * k) (2 * a * m)).run G
      ((HeavyEligibility.program C (4 * k) m).run G input) = _
    rw [hi]
  intro v hv
  have hh := (SelectCorrect.invariant G C (4 * k) active E (H.min' hne) hs har (2 * a * m)).2
    v (decide_eq_true hv)
  change ((HeavyListing.program C (4 * k) a m).run G input v).chosen = _
  rw [hrun]
  simpa only [he] using hh
end Paper.HeavyListShape
