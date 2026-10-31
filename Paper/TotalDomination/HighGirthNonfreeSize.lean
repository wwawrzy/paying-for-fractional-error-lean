import Paper.TotalDomination.HighGirthRetainedParts

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem internal_walk_component
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    {u v : V} (p : G.Walk u v) (hu : u ∈ componentMembers G x identifier hfree C)
    (hs : ∀ z ∈ p.support, z ∈ core G x identifier hfree) :
    v ∈ componentMembers G x identifier hfree C := by
  induction p with
  | nil => exact hu
  | @cons u v w ha p ih =>
    have hv : v ∈ core G x identifier hfree := hs v (by simp)
    exact ih (component_adj_closed G x identifier hfree C hu hv ha) (fun z hz => hs z (by simp [hz]))

theorem freeVertices_walk_closed {u v : V} (p : G.Walk u v)
    (hu : u ∈ freeVertices G x identifier hfree)
    (hs : ∀ z ∈ p.support, z ∈ core G x identifier hfree) : v ∈ freeVertices G x identifier hfree := by
  classical
  obtain ⟨C,hC,huC⟩ := Finset.mem_biUnion.mp hu
  exact Finset.mem_biUnion.mpr ⟨C,hC,internal_walk_component G x identifier hfree C p huC hs⟩

theorem nonfree_of_walk {u v : V} (p : G.Walk u v)
    (hu : u ∈ nonfreeVertices G x identifier hfree)
    (hs : ∀ z ∈ p.support, z ∈ core G x identifier hfree) : v ∈ nonfreeVertices G x identifier hfree := by
  refine Finset.mem_sdiff.mpr ⟨hs v p.end_mem_support,?_⟩
  intro hv
  exact (Finset.mem_sdiff.mp hu).2 (freeVertices_walk_closed G x identifier hfree p.reverse hv
    (fun z hz => hs z (by simpa using hz)))

theorem nonfree_access_cover : nonfreeVertices G x identifier hfree ⊆
    (nonfreeAttachments G x identifier hfree).biUnion (DegreeTwoBalls.ballThree G (core G x identifier hfree)) ∪
    (served G (I G x identifier hfree)).biUnion (DegreeTwoBalls.accessThree G (core G x identifier hfree)) := by
  classical
  intro u hu
  have huS := (Finset.mem_sdiff.mp hu).1
  rcases short_access G x identifier hfree huS with
    ⟨b,hb,q,hq,hlen,hs⟩ | ⟨b,hb,q,hq,hlen,hs⟩ | ⟨y,hy,q,hq,hlen,hs⟩
  · have hbA := branch_attachment G x identifier hfree hb
    have hbN := nonfree_of_walk G x identifier hfree q hu hs
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_inter.mpr ⟨hbA,hbN⟩,?_⟩
    apply DegreeTwoBalls.endpoint_mem_ballThree G (core G x identifier hfree) q.reverse
    · simpa using hlen
    · intro z hz
      exact hs z (by simpa using hz)
  · have hbN := nonfree_of_walk G x identifier hfree q hu hs
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_inter.mpr ⟨hb,hbN⟩,?_⟩
    apply DegreeTwoBalls.endpoint_mem_ballThree G (core G x identifier hfree) q.reverse
    · simpa using (show q.length ≤ 3 by omega)
    · intro z hz
      exact hs z (by simpa using hz)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨y,hy,?_⟩
    apply DegreeTwoBalls.endpoint_mem_accessThree G (core G x identifier hfree) q.reverse
    · simpa using hlen
    · exact huS
    · exact served_not_core G x identifier hfree hy
    · intro z hz
      exact hs z (by simpa using hz)

theorem nonfree_size_bound : (nonfreeVertices G x identifier hfree).card ≤
    7*(nonfreeAttachments G x identifier hfree).card + 6*(served G (I G x identifier hfree)).card := by
  have hA : ((nonfreeAttachments G x identifier hfree).biUnion
      (DegreeTwoBalls.ballThree G (core G x identifier hfree))).card ≤ 7*(nonfreeAttachments G x identifier hfree).card := by
    calc
      _ ≤ ∑ a ∈ nonfreeAttachments G x identifier hfree, (DegreeTwoBalls.ballThree G (core G x identifier hfree) a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ nonfreeAttachments G x identifier hfree, 7 := Finset.sum_le_sum fun a ha =>
        DegreeTwoBalls.card_ballThree G _ (core_neighbor_degree G x identifier hfree)
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
      _ = _ := by simp [Nat.mul_comm]
  have hY : ((served G (I G x identifier hfree)).biUnion
      (DegreeTwoBalls.accessThree G (core G x identifier hfree))).card ≤ 6*(served G (I G x identifier hfree)).card := by
    calc
      _ ≤ ∑ y ∈ served G (I G x identifier hfree), (DegreeTwoBalls.accessThree G (core G x identifier hfree) y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ served G (I G x identifier hfree), 6 := Finset.sum_le_sum fun y hy => served_access_card G x identifier hfree hy
      _ = _ := by simp [Nat.mul_comm]
  have hc := Finset.card_le_card (nonfree_access_cover G x identifier hfree)
  have hU := Finset.card_union_le
    ((nonfreeAttachments G x identifier hfree).biUnion (DegreeTwoBalls.ballThree G (core G x identifier hfree)))
    ((served G (I G x identifier hfree)).biUnion (DegreeTwoBalls.accessThree G (core G x identifier hfree)))
  omega

end Paper.TotalDomination.HighGirthSetup
