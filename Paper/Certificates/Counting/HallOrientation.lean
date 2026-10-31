import Paper.Preliminaries.MinorDensity
import Mathlib.Combinatorics.Hall.Basic

/-! Capacitated Hall constructs a genuine orientation of bounded outdegree.
Paper label: lem:orientation. -/
namespace Paper.HallOrientation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Endpoints of an arbitrary family of actual graph edges. -/
def endpoints (S : Finset G.edgeFinset) : Finset V :=
  S.biUnion (fun e => e.val.toFinset)

theorem edge_family_card_le (S : Finset G.edgeFinset) :
    S.card ≤ G.inducedEdgeCount (endpoints G S) := by
  classical
  let U := endpoints G S
  have hmap := G.map_edgeFinset_induce (s := (U : Set V))
  have hsub : S.map (Function.Embedding.subtype (fun e => e ∈ G.edgeFinset)) ⊆
      G.edgeFinset ∩ U.sym2 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp he
    refine Finset.mem_inter.mpr ⟨q.property, Finset.mem_sym2_iff.mpr ?_⟩
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨q, hq, Sym2.mem_toFinset.mpr hv⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map] at hc
  have he : (G.edgeFinset ∩ U.sym2).card = (G.induce (U : Set V)).edgeFinset.card := by
    have h := congrArg Finset.card hmap
    simpa only [Finset.card_map, Finset.toFinset_coe, SimpleGraph.edgeFinset,
      Set.toFinset_card, Fintype.card_eq_nat_card] using h.symm
  exact hc.trans_eq he

/-- Hall's right side has a slots at each endpoint. -/
theorem slots_union (a : ℕ) (S : Finset G.edgeFinset) :
    S.biUnion (fun e => e.val.toFinset ×ˢ (Finset.univ : Finset (Fin a))) =
      endpoints G S ×ˢ (Finset.univ : Finset (Fin a)) := by
  ext p
  simp only [endpoints, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_univ, and_true]

theorem exists_slots (a : ℕ)
    (hden : ∀ S : Finset V, G.inducedEdgeCount S ≤ a * S.card) :
    ∃ f : G.edgeFinset → V × Fin a,
      Function.Injective f ∧ ∀ e, (f e).1 ∈ e.val.toFinset := by
  classical
  have hHall : ∀ S : Finset G.edgeFinset, S.card ≤
      (S.biUnion (fun e => e.val.toFinset ×ˢ (Finset.univ : Finset (Fin a)))).card := by
    intro S
    rw [slots_union, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have h := (edge_family_card_le G S).trans (hden (endpoints G S))
    simpa only [mul_comm] using h
  obtain ⟨f, hf, hm⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun e : G.edgeFinset => e.val.toFinset ×ˢ (Finset.univ : Finset (Fin a)))).mp hHall
  exact ⟨f, hf, fun e => (Finset.mem_product.mp (hm e)).1⟩

/-- Each undirected edge is oriented away from its assigned endpoint.
The injective slot assignment is a finite certificate of the capacity bound. -/
structure Orientation (a : ℕ) where
  slot : G.edgeFinset → V × Fin a
  injective : Function.Injective slot
  incident : ∀ e, (slot e).1 ∈ e.val.toFinset

theorem exists_orientation (a : ℕ)
    (hden : ∀ S : Finset V, G.inducedEdgeCount S ≤ a * S.card) :
    Nonempty (Orientation G a) := by
  obtain ⟨f, hf, hm⟩ := exists_slots G a hden
  exact ⟨⟨f, hf, hm⟩⟩

noncomputable def tail {a : ℕ} (O : Orientation G a) (e : G.edgeFinset) : V := (O.slot e).1

noncomputable def outEdges {a : ℕ} (O : Orientation G a) (v : V) : Finset G.edgeFinset := by
  classical
  exact Finset.univ.filter (fun e => tail G O e = v)

theorem outEdges_card_le {a : ℕ} (O : Orientation G a) (v : V) :
    (outEdges G O v).card ≤ a := by
  classical
  have hmap : ∀ e ∈ outEdges G O v, (O.slot e).2 ∈ (Finset.univ : Finset (Fin a)) :=
    fun _ _ => Finset.mem_univ _
  have hinj : Set.InjOn (fun e => (O.slot e).2) (outEdges G O v : Set G.edgeFinset) := by
    intro e he f hf hef
    have he' : (O.slot e).1 = v := (Finset.mem_filter.mp he).2
    have hf' : (O.slot f).1 = v := (Finset.mem_filter.mp hf).2
    exact O.injective (Prod.ext (he'.trans hf'.symm) hef)
  have h := Finset.card_le_card_of_injOn (fun e => (O.slot e).2) hmap hinj
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- The real density parameter only has to be bounded by the integer capacity. -/
theorem exists_orientation_of_density {t : ℝ} (hden : Incidence.InducedDensityBound G t)
    (a : ℕ) (ha : t ≤ a) : Nonempty (Orientation G a) := by
  apply exists_orientation G a
  intro S
  have h := (hden S).trans (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg S.card))
  exact_mod_cast h
end Paper.HallOrientation
