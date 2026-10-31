import Paper.Averaging.Tasks.PhysicalTasks
import Paper.Preliminaries.ShortChains

/-! Every actual owner edge inside a task part has a physical walk of
length at most four, entirely contained in that actual task graph. -/
namespace Paper.TaskRootRoutes
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def root (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (i : ↥(I : Set (Low D Q))) : ↥(PhysicalTasks.vertices G D R L Q I : Set V) :=
  ⟨i.val.val.val, PhysicalTasks.root_mem G D R L Q I i.val i.property⟩

set_option maxHeartbeats 1000000 in
theorem edge_route (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    {i j : ↥(I : Set (Low D Q))} (ha : ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q))).Adj i j) :
    ∃ p : (PhysicalTasks.graph G D R L Q I).Walk (root G D R L Q I i) (root G D R L Q I j), p.length ≤ 4 := by
  classical
  let H := PhysicalTasks.vertices G D R L Q I
  obtain ⟨_, m, hmi, hmj⟩ := ha
  obtain ⟨r, hr, hri⟩ := Finset.mem_image.mp hmi
  obtain ⟨s, hs, hsj⟩ := Finset.mem_image.mp hmj
  have hiH : i.val.val.val ∈ H := PhysicalTasks.root_mem G D R L Q I i.val i.property
  have hjH : j.val.val.val ∈ H := PhysicalTasks.root_mem G D R L Q I j.val j.property
  have hiC : i.val.val.val ∈ PhysicalTasks.centers D Q I := Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
  have hrH : r ∈ H := PhysicalTasks.star_mem G D R L Q I (by simpa only [hri] using hiC)
  have hjC : j.val.val.val ∈ PhysicalTasks.centers D Q I := Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
  have hsH : s ∈ H := PhysicalTasks.star_mem G D R L Q I (by simpa only [hsj] using hjC)
  have hmLight : m ∉ HeavyRepair.heavy G D R L := by
    intro hm
    rw [OwnerInteraction.heavy_empty G D R L hm] at hmi
    exact Finset.notMem_empty _ hmi
  have hmH : m ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr
    ⟨hmLight, ⟨i.val.val.val, Finset.mem_inter.mpr ⟨hmi, hiC⟩⟩⟩⟩
  have h₀ : i.val.val.val = r ∨ G.Adj i.val.val.val r := by simpa only [hri] using OwnerExperiment.owner_star G D r
  have h₁ : r = m ∨ G.Adj r m :=
    ((mem_closed G r m).mp (Finset.mem_inter.mp hr).1).elim Or.inl (fun h => Or.inr h.symm)
  have h₂ : m = s ∨ G.Adj m s :=
    ((mem_closed G s m).mp (Finset.mem_inter.mp hs).1).elim (fun h => Or.inl h.symm) Or.inr
  have h₃ : s = j.val.val.val ∨ G.Adj s j.val.val.val := by
    have h := OwnerExperiment.owner_star G D s
    rw [hsj] at h
    exact h.elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)
  obtain ⟨p, hp, hps⟩ := ShortChains.chain5 G i.val.val.val r m s j.val.val.val h₀ h₁ h₂ h₃
  have hset : ({i.val.val.val, r, m, s, j.val.val.val} : Finset V) ⊆ H := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hiH, hrH, hmH, hsH, hjH⟩
  have hpH : ∀ z ∈ p.support, z ∈ H := fun z hz => hset (hps z hz)
  refine ⟨p.induce (H : Set V) hpH, ?_⟩
  exact (ShortChains.induce_length G H p hpH).trans_le hp
end Paper.TaskRootRoutes
