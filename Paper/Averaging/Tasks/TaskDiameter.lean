import Paper.Averaging.Tasks.TaskVertexRoutes

/-! The actual physical graph of any connected owner part of size≤k is
connected, and every pair of its vertices has a task walk of length≤4k. -/
namespace Paper.TaskDiameter
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem roots (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q))).Connected)
    (i j : ↥(I : Set (Low D Q))) :
    ∃ p : (PhysicalTasks.graph G D R L Q I).Walk (TaskRootRoutes.root G D R L Q I i) (TaskRootRoutes.root G D R L Q I j),
      p.length ≤ 4 * (I.card - 1) := by
  classical
  obtain ⟨p, hp⟩ := (hI i j).exists_isPath
  have hlen : p.length < I.card := by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hp.length_lt
  obtain ⟨q, hq⟩ := ShortChains.lift_walk (PhysicalTasks.graph G D R L Q I)
    ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q)))
    (TaskRootRoutes.root G D R L Q I) 4 (fun h => TaskRootRoutes.edge_route G D R L Q I h) p
  exact ⟨q, hq.trans (Nat.mul_le_mul_left 4 (by omega))⟩

theorem walk_bound (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (x y : ↥(PhysicalTasks.vertices G D R L Q I : Set V)) :
    ∃ p : (PhysicalTasks.graph G D R L Q I).Walk x y, p.length ≤ 4 * k := by
  classical
  obtain ⟨i, px, hx⟩ := TaskVertexRoutes.near_root G D R L Q I x
  obtain ⟨j, py, hy⟩ := TaskVertexRoutes.near_root G D R L Q I y
  obtain ⟨q, hq⟩ := roots G D R L Q I hI i j
  have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i.val, i.property⟩
  refine ⟨px.append (q.append py.reverse), ?_⟩
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

theorem spec (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    (PhysicalTasks.graph G D R L Q I).Connected ∧
      ∀ x y, ∃ p : (PhysicalTasks.graph G D R L Q I).Walk x y, p.length ≤ 4 * k := by
  have hwalk := walk_bound G D R L Q I hI k hsize
  obtain ⟨i⟩ := hI.nonempty
  letI : Nonempty ↥(PhysicalTasks.vertices G D R L Q I : Set V) :=
    ⟨TaskRootRoutes.root G D R L Q I i⟩
  exact ⟨⟨fun x y => ⟨(hwalk x y).choose⟩⟩, hwalk⟩
end Paper.TaskDiameter
