import GraphTheory.SimpleGraph.Planar.Basic

/-!
# Forbidden configurations for reversing a planar edge contraction

These are the actual minor constructions in the combinatorial core of Wagner's
theorem (Doczkal, ITP 2021, Lemma 12).  Two adjacent apex vertices cannot see
three mutually neighboring connected rim regions; nor can their attachments
alternate around four connected rim regions.  The regions are explicit vertex
sets.  No plane embedding or additional planarity provider is assumed.

This file does not yet construct the regions from arcs of a facial cycle.
-/

namespace PlaneTopology.PlanarMaximalStructure

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two vertex sets have an actual graph edge between them. -/
def Neighboring (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- Set-neighboring is symmetric. -/
theorem Neighboring.symm {A B : Set V} (h : Neighboring G A B) :
    Neighboring G B A := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨b, hb, a, ha, hab.symm⟩

/-- A singleton sees a region exactly when its vertex has a neighbor there. -/
@[simp] theorem neighboring_singleton_left (a : V) (A : Set V) :
    Neighboring G {a} A ↔ ∃ b ∈ A, G.Adj a b := by
  simp [Neighboring]

/-- Two singleton regions are neighboring exactly at an actual graph edge. -/
@[simp] theorem neighboring_singletons (a b : V) :
    Neighboring G {a} {b} ↔ G.Adj a b := by
  simp [Neighboring]

/-- Singleton-induced graphs are connected, including without finiteness. -/
theorem connected_induce_singleton (a : V) : (G.induce {a}).Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨⟨a, rfl⟩, fun ⟨b, hb⟩ => by
    rw [Set.mem_singleton_iff] at hb
    subst b
    exact Reachable.refl _⟩

/-- The K₅ obstruction: adjacent apices both meet each of three disjoint,
connected, pairwise neighboring regions outside the apices. -/
theorem k5_minor_of_three_regions (x y : V) (A : Fin 3 → Set V)
    (hxy : G.Adj x y)
    (hconn : ∀ i, (G.induce (A i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hx : ∀ i, x ∉ A i) (hy : ∀ i, y ∉ A i)
    (hxA : ∀ i, Neighboring G {x} (A i))
    (hyA : ∀ i, Neighboring G {y} (A i))
    (hAA : Pairwise (fun i j => Neighboring G (A i) (A j))) :
    (completeGraph (Fin 5)).IsMinor G := by
  classical
  let B : Fin 5 → Set V := ![{x}, {y}, A 0, A 1, A 2]
  refine ⟨{
    branchSet := B
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    adjacent := ?_ }⟩
  · intro i
    fin_cases i
    · exact ⟨x, rfl⟩
    · exact ⟨y, rfl⟩
    all_goals
      obtain ⟨a⟩ := (hconn _).nonempty
      exact ⟨a.val, a.property⟩
  · intro i j hij
    have hxy' := G.ne_of_adj hxy
    have hyx' := hxy'.symm
    fin_cases i <;> fin_cases j <;>
      simp_all [B, Set.disjoint_singleton_left, Set.disjoint_singleton_right,
        hdisj (by decide : (0 : Fin 3) ≠ 1),
        hdisj (by decide : (0 : Fin 3) ≠ 2),
        hdisj (by decide : (1 : Fin 3) ≠ 0),
        hdisj (by decide : (1 : Fin 3) ≠ 2),
        hdisj (by decide : (2 : Fin 3) ≠ 0),
        hdisj (by decide : (2 : Fin 3) ≠ 1)]
  · intro i
    fin_cases i
    · exact connected_induce_singleton x
    · exact connected_induce_singleton y
    all_goals exact hconn _
  · intro i j hij
    change Neighboring G (B i) (B j)
    have hne : i ≠ j := hij
    have hxx := hxA
    have hyy := hyA
    have hxx' := fun i => (hxA i).symm
    have hyy' := fun i => (hyA i).symm
    have hxy' := hxy.symm
    fin_cases i <;> fin_cases j <;>
      simp_all [B, hAA (by decide : (0 : Fin 3) ≠ 1),
        hAA (by decide : (0 : Fin 3) ≠ 2),
        hAA (by decide : (1 : Fin 3) ≠ 0),
        hAA (by decide : (1 : Fin 3) ≠ 2),
        hAA (by decide : (2 : Fin 3) ≠ 0),
        hAA (by decide : (2 : Fin 3) ≠ 1)]

/-- The three-region obstruction is impossible in a minor-planar graph. -/
theorem not_three_regions_of_isPlanar (hG : G.IsPlanar)
    (x y : V) (A : Fin 3 → Set V)
    (hxy : G.Adj x y)
    (hconn : ∀ i, (G.induce (A i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hx : ∀ i, x ∉ A i) (hy : ∀ i, y ∉ A i)
    (hxA : ∀ i, Neighboring G {x} (A i))
    (hyA : ∀ i, Neighboring G {y} (A i))
    (hAA : Pairwise (fun i j => Neighboring G (A i) (A j))) : False :=
  hG.1 (k5_minor_of_three_regions x y A hxy hconn hdisj hx hy hxA hyA hAA)

/-- The K₃,₃ obstruction: four disjoint connected regions occur in rim order,
and the two adjacent apices attach alternately to them. -/
theorem k33_minor_of_alternating_regions (x y : V) (A : Fin 4 → Set V)
    (hxy : G.Adj x y)
    (hconn : ∀ i, (G.induce (A i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hx : ∀ i, x ∉ A i) (hy : ∀ i, y ∉ A i)
    (hx0 : Neighboring G {x} (A 0)) (hx2 : Neighboring G {x} (A 2))
    (hy1 : Neighboring G {y} (A 1)) (hy3 : Neighboring G {y} (A 3))
    (hcycle : ∀ i : Fin 4, Neighboring G (A i) (A (i + 1))) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).IsMinor G := by
  classical
  let B : Fin 3 ⊕ Fin 3 → Set V :=
    Sum.elim ![{x}, A 1, A 3] ![{y}, A 0, A 2]
  refine ⟨{
    branchSet := B
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    adjacent := ?_ }⟩
  · intro i
    rcases i with i | i <;> fin_cases i
    · exact ⟨x, rfl⟩
    · obtain ⟨a⟩ := (hconn 1).nonempty; exact ⟨a.val, a.property⟩
    · obtain ⟨a⟩ := (hconn 3).nonempty; exact ⟨a.val, a.property⟩
    · exact ⟨y, rfl⟩
    · obtain ⟨a⟩ := (hconn 0).nonempty; exact ⟨a.val, a.property⟩
    · obtain ⟨a⟩ := (hconn 2).nonempty; exact ⟨a.val, a.property⟩
  · intro i j hij
    have hxy' := G.ne_of_adj hxy
    have hyx' := hxy'.symm
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | skip
    all_goals dsimp [B]
    all_goals first
      | exact hdisj (by decide)
      | exact Set.disjoint_singleton_left.mpr (hx _)
      | exact Set.disjoint_singleton_right.mpr (hx _)
      | exact Set.disjoint_singleton_left.mpr (hy _)
      | exact Set.disjoint_singleton_right.mpr (hy _)
      | simpa using hxy'
      | simpa using hyx'
  · intro i
    rcases i with i | i <;> fin_cases i
    · exact connected_induce_singleton x
    · exact hconn 1
    · exact hconn 3
    · exact connected_induce_singleton y
    · exact hconn 0
    · exact hconn 2
  · intro i j hij
    change Neighboring G (B i) (B j)
    have hx0' := hx0.symm
    have hx2' := hx2.symm
    have hy1' := hy1.symm
    have hy3' := hy3.symm
    have hc0 := hcycle 0
    have hc1 := hcycle 1
    have hc2 := hcycle 2
    have hc3 := hcycle 3
    have hc0' := hc0.symm
    have hc1' := hc1.symm
    have hc2' := hc2.symm
    have hc3' := hc3.symm
    have hxy' := hxy.symm
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j
    all_goals simp [completeBipartiteGraph] at hij
    all_goals dsimp [B]
    all_goals first
      | exact hx0 | exact hx2 | exact hy1 | exact hy3
      | exact hx0' | exact hx2' | exact hy1' | exact hy3'
      | exact hc0 | exact hc1 | exact hc2 | exact hc3
      | exact hc0' | exact hc1' | exact hc2' | exact hc3'
      | exact (neighboring_singletons x y).mpr hxy
      | exact (neighboring_singletons y x).mpr hxy'

/-- Alternating rim attachments are impossible in a minor-planar graph. -/
theorem not_alternating_regions_of_isPlanar (hG : G.IsPlanar)
    (x y : V) (A : Fin 4 → Set V)
    (hxy : G.Adj x y)
    (hconn : ∀ i, (G.induce (A i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hx : ∀ i, x ∉ A i) (hy : ∀ i, y ∉ A i)
    (hx0 : Neighboring G {x} (A 0)) (hx2 : Neighboring G {x} (A 2))
    (hy1 : Neighboring G {y} (A 1)) (hy3 : Neighboring G {y} (A 3))
    (hcycle : ∀ i : Fin 4, Neighboring G (A i) (A (i + 1))) : False :=
  hG.2 (k33_minor_of_alternating_regions x y A hxy hconn hdisj hx hy
    hx0 hx2 hy1 hy3 hcycle)

end PlaneTopology.PlanarMaximalStructure

#print axioms PlaneTopology.PlanarMaximalStructure.k5_minor_of_three_regions
#print axioms PlaneTopology.PlanarMaximalStructure.not_three_regions_of_isPlanar
#print axioms PlaneTopology.PlanarMaximalStructure.k33_minor_of_alternating_regions
#print axioms PlaneTopology.PlanarMaximalStructure.not_alternating_regions_of_isPlanar
