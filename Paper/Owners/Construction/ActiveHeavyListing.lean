import Paper.Owners.Construction.HeavyListShape
import Paper.Averaging.Tasks.ActiveTaskContext

/-! Actual heavy flags and complete fixed heavy-list execution on general active tasks. -/
namespace Paper.ActiveHeavyListing
open BroadcastModel HeavyEligibility HeavyListShape
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (K : ActiveTask.Context G)

theorem heavy_flag {b : ℕ} (C : BitCode V b)
    (A : Finset V)
    (hA : A ⊆ K.vertices) (m : ℕ) :
    ∀ v ∈ K.vertices,
      ((program C K.diameter m).run G
        (fun u => (decide (u ∈ K.vertices), decide (u ∈ A))) v).2 =
          decide (A.card ≤ m * (SevenFoundation.closed G v ∩ A).card) := by
  have hi : (fun u => countInput b
      (decide (u ∈ K.vertices), decide (u ∈ A))) =
      fun u => (decide (u ∈ K.vertices),
        fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0)) := by
    funext u
    simp [countInput]
  intro v hv
  have hcounts := ActiveTaskQueries.counts G C K.vertices K.nonempty K.diameter 1 K.paths (fun _ => A) (fun _ => hA) v hv
  have hscalar := congrArg (Option.map (fun f : Fin 1 → ℕ => f 0)) hcounts
  simp only [Option.map_map, Option.map_some] at hscalar
  change (((TaskQueries.countProgram C 1 K.diameter).run G
    (fun u => (decide (u ∈ K.vertices),
      fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0))) v).2.map
        (fun f => (f 0).value.val)) = some A.card at hscalar
  rw [run_program, hi]
  change (match _ with
    | none => false
    | some a => decide (a ≤ m * (NeighborhoodCount.program.run G (fun u => decide (u ∈ A)) v))) = _
  rw [hscalar, NeighborhoodCount.eval_eq]

theorem chosen {b : ℕ} (C : BitCode V b)
    (A : Finset V)
    (hA : A ⊆ K.vertices) (a m : ℕ) :
    ∀ v ∈ K.vertices,
      ((HeavyListing.program C K.diameter a m).run G
        (fun u => (decide (u ∈ K.vertices), decide (u ∈ A))) v).chosen =
          initialList G (K.vertices) A a m := by
  let H := K.vertices
  let active : V → Bool := fun v => decide (v ∈ H)
  let input : V → Bool × Bool := fun v => (active v, decide (v ∈ A))
  let E : V → Bool := fun v => ((HeavyEligibility.program C K.diameter m).run G input v).2
  have hE (v : V) (hv : v ∈ H) : E v =
      decide (A.card ≤ m * (SevenFoundation.closed G v ∩ A).card) :=
    heavy_flag G K C A hA m v hv
  have he : SelectStep.candidates active E = H ∩ LocalSearchBounds.heavy G A m := by
    ext v
    by_cases hv : v ∈ H
    · simp [SelectStep.candidates, active, hv, hE v hv, LocalSearchBounds.heavy]
    · simp [SelectStep.candidates, active, hv]
  have hne := K.nonempty
  have hs := ActiveTask.tree G K C
  have har : active (H.min' hne) = true := decide_eq_true (Finset.min'_mem _ hne)
  have hi : (HeavyEligibility.program C K.diameter m).run G input = fun v => (active v, E v) := by
    funext v
    exact Prod.ext (HeavyEligibility.active G C K.diameter m input v) rfl
  have hrun : (HeavyListing.program C K.diameter a m).run G input =
      (SelectProtocol.program C K.diameter (2 * a * m)).run G (fun v => (active v, E v)) := by
    change (SelectProtocol.program C K.diameter (2 * a * m)).run G
      ((HeavyEligibility.program C K.diameter m).run G input) = _
    rw [hi]
  intro v hv
  have hh := (SelectCorrect.invariant G C K.diameter active E (H.min' hne) hs har (2 * a * m)).2
    v (decide_eq_true hv)
  change ((HeavyListing.program C K.diameter a m).run G input v).chosen = _
  rw [hrun]
  simpa only [he] using hh
end Paper.ActiveHeavyListing
