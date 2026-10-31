import Paper.Averaging.Tasks.ActiveTaskContext
import Paper.Averaging.Tasks.MaskedTaskCover

/-! A role may be stored at extra inactive nodes. Masking by any superset
of the actual task preserves its active geometry and benchmark. -/
namespace Paper.SuperMaskedTask
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem induced_eq (F H : Finset V) (hHF : H ⊆ F) :
    (MaskedTaskGraph.graph G F).induce (H : Set V) = G.induce (H : Set V) := by
  ext u v
  change (G.Adj u.val v.val ∧ u.val ∈ F ∧ v.val ∈ F) ↔ G.Adj u.val v.val
  exact ⟨fun h => h.1, fun h => ⟨h, hHF u.property, hHF v.property⟩⟩

noncomputable def physical (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (F : Finset V) (hHF : PhysicalTasks.vertices G D R L Q I ⊆ F) :
    ActiveTask.Context (MaskedTaskGraph.graph G F) where
  vertices := PhysicalTasks.vertices G D R L Q I
  nonempty := by
    obtain ⟨v⟩ := (TaskDiameter.spec G D R L Q I hI k hsize).1.nonempty
    exact ⟨v.val, v.property⟩
  diameter := 4 * k
  paths := by
    intro x y
    rw [induced_eq G F _ hHF]
    exact (TaskDiameter.spec G D R L Q I hI k hsize).2 x y

theorem cover (F H : Finset V) (hHF : H ⊆ F) (d p : V → ℕ)
    (hd : ∀ r, r ∉ H → d r = 0) (hp : ∀ u, u ∉ H → p u = 0)
    (hcover : ∀ r, d r ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∀ r, d r ≤ ∑ u ∈ SevenFoundation.closed (MaskedTaskGraph.graph G F) r, p u :=
  MaskedTaskCover.cover G F d p
    (fun r hr => hd r (fun h => hr (hHF h))) (fun u hu => hp u (fun h => hu (hHF h))) hcover

theorem valid_original (F H : Finset V) {B q m : ℕ}
    (c : V → Fin (B + 1)) (d : V → Fin (q + 1)) (w : SolutionWord.Word V B)
    (hw : SearchSpec.Valid (MaskedTaskGraph.graph G F) H c d m w) : SearchSpec.Valid G H c d m w := by
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
  intro r
  exact (hw.2.2.2 r).trans (Finset.sum_le_sum_of_subset_of_nonneg (MaskedTaskCover.closed_subset G F r)
    (fun _ _ _ => Nat.zero_le _))
end Paper.SuperMaskedTask
