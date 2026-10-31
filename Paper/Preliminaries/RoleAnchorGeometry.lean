import Paper.Averaging.Tasks.TaskRoleId
import Paper.Preliminaries.CandidateGeometry
import Paper.Owners.Construction.OwnerVirtualFacts
import Paper.Averaging.Tasks.PhysicalTasks

/-! Actual owner/task geometry bounds all possible task anchors seen by
a physical vertex, even when the task's physical vertex count is unbounded. -/
namespace Paper.RoleAnchorGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def roots (D S : Finset V) (L : ℕ) (v : V) : Finset V :=
  insert (OwnerSupport.owner G D v) (OwnerInteraction.actualSupport G D S L v)

theorem roots_card (D S : Finset V) (L : ℕ) (v : V) : (roots G D S L v).card ≤ L + 1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (OwnerInteraction.support_bound G D S L v) 1)

noncomputable def anchors (D S : Finset V) (L Δ k : ℕ) (v : V) : Finset V :=
  (roots G D S L v).biUnion (fun u => NeighborBalls.ball
    (fun w => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset w) u k)

theorem anchors_card (D S : Finset V) (L Δ k : ℕ) (v : V) :
    (anchors G D S L Δ k v).card ≤ (L + 1) * (Δ + 1) ^ k := by
  calc
    _ ≤ ∑ u ∈ roots G D S L v, (NeighborBalls.ball
        (fun w => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset w) u k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ roots G D S L v, (Δ + 1) ^ k := Finset.sum_le_sum (fun u _ =>
      NeighborBallGraph.graph_card_bound _ Δ (PublicOwners.degree_bound G D S L Δ) u k)
    _ = (roots G D S L v).card * (Δ + 1) ^ k := by simp only [Finset.sum_const_nat]
    _ ≤ _ := Nat.mul_le_mul_right _ (roots_card G D S L v)

theorem centers_connected (D S : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D S L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected) :
    ((PublicOwners.graph G D S L Q).induce (PhysicalTasks.centers D Q I : Set V)).Connected := by
  have hc := WeakProjection.connected_image (OwnerTasks.graph G D S L Q) (PublicOwners.graph G D S L Q)
    (fun i : OwnerTasks.Low D Q => i.val.val)
    (fun i j ha => Or.inr ((PublicEmbedding.adj_iff (OwnerTasks.graph G D S L Q)
      (PublicOwners.embedding D Q) _ _).mpr ⟨i, j, ha, rfl, rfl⟩))
    (I : Set (OwnerTasks.Low D Q)) hI
  have he : (fun i : OwnerTasks.Low D Q => i.val.val) '' (I : Set (OwnerTasks.Low D Q)) =
      (PhysicalTasks.centers D Q I : Set V) := by
    ext v
    simp only [Set.mem_image, Finset.mem_coe, PhysicalTasks.centers, Finset.mem_image]
  rwa [he] at hc

theorem touches (D S : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (OwnerTasks.Low D Q)) (v : V) (hv : v ∈ PhysicalTasks.vertices G D S L Q I) :
    ∃ u ∈ roots G D S L v, u ∈ PhysicalTasks.centers D Q I := by
  unfold PhysicalTasks.vertices at hv
  have hi : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hi] at hv
  rcases (Finset.mem_filter.mp hv).2 with ho | ⟨_, u, hu⟩
  · exact ⟨OwnerSupport.owner G D v, Finset.mem_insert_self _ _, ho⟩
  · exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hu).2⟩

theorem anchor_mem (D S : Finset V) (L Δ k : ℕ)
    (I : Finset (OwnerTasks.Low D (OwnerVirtualFacts.high G D S L Δ)))
    (hI : ((OwnerTasks.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).induce (I : Set _)).Connected)
    (hsize : I.card ≤ k) (v a : V) (hv : v ∈ PhysicalTasks.vertices G D S L (OwnerVirtualFacts.high G D S L Δ) I)
    (ha : a ∈ PhysicalTasks.centers D (OwnerVirtualFacts.high G D S L Δ) I) : a ∈ anchors G D S L Δ k v := by
  obtain ⟨u, hu, huI⟩ := touches G D S L _ I v hv
  apply Finset.mem_biUnion.mpr
  refine ⟨u, hu, ?_⟩
  have hc := centers_connected G D S L _ I hI
  have hs : (PhysicalTasks.centers D (OwnerVirtualFacts.high G D S L Δ) I).card ≤ k :=
    (PhysicalTasks.centers_card D _ I).trans_le hsize
  have hh := CandidateGeometry.connected_subset_ball _ _ hc k hs u huI u 0 (NeighborBalls.self_mem _ u 0) ha
  simpa only [Nat.zero_add] using hh

theorem role_overlap (D S : Finset V) (L Δ k M : ℕ) (v : V) (roles : Finset (TaskRoleId.Id V M))
    (hroles : ∀ r ∈ roles, ∃ I : Finset (OwnerTasks.Low D (OwnerVirtualFacts.high G D S L Δ)),
      ((OwnerTasks.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).induce (I : Set _)).Connected ∧
      I.card ≤ k ∧ v ∈ PhysicalTasks.vertices G D S L (OwnerVirtualFacts.high G D S L Δ) I ∧
      (ofLex r).1 ∈ PhysicalTasks.centers D (OwnerVirtualFacts.high G D S L Δ) I) :
    roles.card ≤ ((L + 1) * (Δ + 1) ^ k) * M := by
  apply (TaskRoleId.overlap_bound (anchors G D S L Δ k v) M roles _).trans
    (Nat.mul_le_mul_right M (anchors_card G D S L Δ k v))
  intro r hr
  obtain ⟨I, hI, hsize, hv, ha⟩ := hroles r hr
  exact anchor_mem G D S L Δ k I hI hsize v (ofLex r).1 hv ha
end Paper.RoleAnchorGeometry
