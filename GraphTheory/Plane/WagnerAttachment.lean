import GraphTheory.Plane.CyclicAttachment
import GraphTheory.Plane.CycleRimRegions

/-!
# The actual planar cycle-attachment theorem

For two adjacent vertices outside an actual graph cycle, minor exclusion
forces all neighbors of one vertex on the cycle into a closed gap between
consecutive neighbors of the other. This discharges the combinatorial
ordering step of the constructive Wagner argument; no embedding is assumed.
-/

namespace PlaneTopology.WagnerAttachment

open SimpleGraph PlaneTopology.CyclicAttachment PlaneTopology.CycleRimRegions

variable {V : Type*}
  {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}

/-- Actual positions of the neighbors of x along a closed graph walk. -/
def cycleAttachments (p : G.Walk z z) (x : V) : Finset ℕ :=
  (Finset.range p.length).filter (fun i ↦ G.Adj x (p.getVert i))

/-- Position membership means a genuine neighbor at an in-range cycle index. -/
@[simp] theorem mem_cycleAttachments (p : G.Walk z z) (x : V) (i : ℕ) :
    i ∈ cycleAttachments p x ↔ i < p.length ∧ G.Adj x (p.getVert i) := by
  simp [cycleAttachments]

/-- Three common neighbors on an actual cycle produce a forbidden K₅ minor. -/
theorem card_common_attachments_le_two (hG : G.IsPlanar)
    (p : G.Walk z z) (hp : p.IsCycle) (x y : V) (hxy : G.Adj x y)
    (hx : x ∉ p.support) (hy : y ∉ p.support) :
    (cycleAttachments p x ∩ cycleAttachments p y).card ≤ 2 := by
  apply card_le_two_of_no_increasing_triple
  intro a ha b hb c hc habc
  obtain ⟨haX, haY⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbX, hbY⟩ := Finset.mem_inter.mp hb
  obtain ⟨hcX, hcY⟩ := Finset.mem_inter.mp hc
  simp only [mem_cycleAttachments] at haX haY hbX hbY hcX hcY
  exact hG.1 (k5_minor_of_ordered_cycle_neighbors p hp x y hxy hx hy a b c
    habc.1 habc.2 hcX.1 haX.2 hbX.2 hcX.2 haY.2 hbY.2 hcY.2)

/-- Alternating actual neighbors on a cycle produce a forbidden K₃,₃ minor.
The four linear orders account explicitly for the wrap-around cases. -/
theorem attachments_nonalternating (hG : G.IsPlanar)
    (p : G.Walk z z) (hp : p.IsCycle) (x y : V) (hxy : G.Adj x y)
    (hx : x ∉ p.support) (hy : y ∉ p.support) :
    Nonalternating (cycleAttachments p x) (cycleAttachments p y) := by
  intro a ha b hb c hc d hd hne hcross
  simp only [mem_cycleAttachments] at ha hb hc hd
  obtain ⟨hacb, hbda⟩ := hcross
  by_cases hab : a < b
  · have hacb' : a < c ∧ c < b := by simpa [openArc, hab] using hacb
    have hbda' : b < d ∨ d < a := by simpa [openArc, show ¬b < a by omega] using hbda
    rcases hbda' with hbd | hda
    · exact hG.2 (k33_minor_of_ordered_cycle_neighbors p hp x y hxy hx hy
        a c b d hacb'.1 hacb'.2 hbd hd.1 ha.2 hb.2 hc.2 hd.2)
    · exact hG.2 (k33_minor_of_ordered_cycle_neighbors p hp y x hxy.symm hy hx
        d a c b hda hacb'.1 hacb'.2 hb.1 hd.2 hc.2 ha.2 hb.2)
  · have hba : b < a := by omega
    have hacb' : a < c ∨ c < b := by simpa [openArc, hab] using hacb
    have hbda' : b < d ∧ d < a := by simpa [openArc, hba] using hbda
    rcases hacb' with hac | hcb
    · exact hG.2 (k33_minor_of_ordered_cycle_neighbors p hp x y hxy hx hy
        b d a c hbda'.1 hbda'.2 hac hc.1 hb.2 ha.2 hd.2 hc.2)
    · exact hG.2 (k33_minor_of_ordered_cycle_neighbors p hp y x hxy.symm hy hx
        c b d a hcb hbda'.1 hbda'.2 ha.1 hc.2 hd.2 hb.2 ha.2)

/-- The genuine combinatorial core of the planar vertex-splitting step:
minor planarity, actual cycle edges and actual neighbor positions supply the
consecutive-gap conclusion without any geometric or numerical provider. -/
theorem exists_neighbor_gap_of_isPlanar (hG : G.IsPlanar)
    (p : G.Walk z z) (hp : p.IsCycle) (x y : V) (hxy : G.Adj x y)
    (hx : x ∉ p.support) (hy : y ∉ p.support)
    (hX : 2 ≤ (cycleAttachments p x).card) (hY : 2 ≤ (cycleAttachments p y).card) :
    ∃ a b, Consecutive (cycleAttachments p x) a b ∧
      ∀ i ∈ cycleAttachments p y, closedArc a b i :=
  exists_gap_of_nonalt hX hY (card_common_attachments_le_two hG p hp x y hxy hx hy)
    (attachments_nonalternating hG p hp x y hxy hx hy)

#print axioms card_common_attachments_le_two
#print axioms attachments_nonalternating
#print axioms exists_neighbor_gap_of_isPlanar

end PlaneTopology.WagnerAttachment
