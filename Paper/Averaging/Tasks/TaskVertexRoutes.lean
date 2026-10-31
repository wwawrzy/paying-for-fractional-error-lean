import Paper.Averaging.Tasks.TaskRootRoutes

/-! Every actual physical task vertex is within two task edges of an
owner in the part. All intermediate physical vertices remain in the task. -/
namespace Paper.TaskVertexRoutes
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem near_root (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (x : ↥(PhysicalTasks.vertices G D R L Q I : Set V)) :
    ∃ i : ↥(I : Set (Low D Q)), ∃ p : (PhysicalTasks.graph G D R L Q I).Walk x (TaskRootRoutes.root G D R L Q I i),
      p.length ≤ 2 := by
  classical
  let H := PhysicalTasks.vertices G D R L Q I
  rcases (Finset.mem_filter.mp x.property).2 with hstar | ⟨_, hmeet⟩
  · obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hstar
    let j : ↥(I : Set (Low D Q)) := ⟨i, hi⟩
    have hiH : i.val.val ∈ H := PhysicalTasks.root_mem G D R L Q I i hi
    have ho := OwnerExperiment.owner_star G D x.val
    rw [← hieq] at ho
    have hstep : x.val = i.val.val ∨ G.Adj x.val i.val.val :=
      ho.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    obtain ⟨p, hp, hps⟩ := ShortChains.step G hstep
    have hpH : ∀ z ∈ p.support, z ∈ H := by
      intro z hz
      rcases hps z hz with he | he
      · simpa only [he] using x.property
      · simpa only [he] using hiH
    refine ⟨j, p.induce (H : Set V) hpH, ?_⟩
    exact (ShortChains.induce_length G H p hpH).trans_le (hp.trans (by omega))
  · obtain ⟨d, hd⟩ := hmeet
    have hd' := Finset.mem_inter.mp hd
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hd'.2
    obtain ⟨r, hr, hrEq⟩ := Finset.mem_image.mp hd'.1
    have hri : OwnerSupport.owner G D r = i.val.val := hrEq.trans hieq.symm
    let j : ↥(I : Set (Low D Q)) := ⟨i, hi⟩
    have hiH : i.val.val ∈ H := PhysicalTasks.root_mem G D R L Q I i hi
    have hiC : i.val.val ∈ PhysicalTasks.centers D Q I := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hrH : r ∈ H := PhysicalTasks.star_mem G D R L Q I (by simpa only [hri] using hiC)
    have h₀ : x.val = r ∨ G.Adj x.val r :=
      ((mem_closed G r x.val).mp (Finset.mem_inter.mp hr).1).elim (fun h => Or.inl h.symm) Or.inr
    have h₁ : r = i.val.val ∨ G.Adj r i.val.val := by
      have ho := OwnerExperiment.owner_star G D r
      rw [hri] at ho
      exact ho.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    obtain ⟨p, hp, hps⟩ := ShortChains.chain3 G x.val r i.val.val h₀ h₁
    have hset : ({x.val, r, i.val.val} : Finset V) ⊆ H := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨x.property, hrH, hiH⟩
    have hpH : ∀ z ∈ p.support, z ∈ H := fun z hz => hset (hps z hz)
    refine ⟨j, p.induce (H : Set V) hpH, ?_⟩
    exact (ShortChains.induce_length G H p hpH).trans_le hp
end Paper.TaskVertexRoutes
