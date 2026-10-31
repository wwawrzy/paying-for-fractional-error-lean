import GraphTheory.Surfaces.SignedRotationGirthFaces
import GraphTheory.Surfaces.SignedRotationSubgraphGenus
import GraphTheory.Surfaces.SignedRotationCopyTransport
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
namespace SimpleGraph.SignedRotation
universe u
theorem arbitrary_girth_euler_mul_bound (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ((g : ℤ)-2) * G.edgeFinset.card ≤ (g : ℤ) * (Fintype.card V + r.eulerGenus) := by
  classical
  by_cases hdeg : ∀ v, 2 ≤ G.degree v
  · exact r.girth_euler_mul_bound hdeg g hg3 hg
  · push Not at hdeg
    obtain ⟨v,hv⟩ := hdeg
    let S : Set V := {v}ᶜ
    let H := G.induce S
    obtain ⟨s,hs⟩ := exists_induce_genus_le G r S
    have hHg : ∀ (w : S) (c : H.Walk w w), c.IsCycle → g ≤ c.length := by
      intro w c hc
      let f := (Embedding.induce (G := G) S).toHom
      have hcyc : (c.map f).IsCycle := hc.map (Embedding.induce (G := G) S).injective
      have hh := hg w.val (c.map f) hcyc
      have hlen : (c.map f).length = c.length := Walk.length_map f c
      exact hlen ▸ hh
    have ih := arbitrary_girth_euler_mul_bound S H s g hg3 hHg
    have heN : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
      exact (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
    have he : (H.edgeFinset.card : ℤ) = (G.edgeFinset.card : ℤ) - G.degree v := by
      rw [heN,Nat.cast_sub (G.degree_le_card_edgeFinset v)]
    have hnN : Fintype.card S + 1 = Fintype.card V := by
      have hh := Fintype.card_subtype_compl (fun w : V => w = v)
      simp only [Fintype.card_subtype_eq] at hh
      change Fintype.card S = Fintype.card V - 1 at hh
      letI : Nonempty V := ⟨v⟩
      have hp : 0 < Fintype.card V := Fintype.card_pos
      omega
    have hn : (Fintype.card S : ℤ) + 1 = Fintype.card V := by exact_mod_cast hnN
    have hd : (G.degree v : ℤ) ≤ 1 := by exact_mod_cast (show G.degree v ≤ 1 by omega)
    have hgn : (3 : ℤ) ≤ g := by exact_mod_cast hg3
    rw [he] at ih
    nlinarith
termination_by Fintype.card V
decreasing_by
  exact Fintype.card_subtype_lt (x := v) (by simp [S])
theorem arbitrary_girth_edge_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (e : ℝ) (he : (r.eulerGenus : ℝ) ≤ e) :
    (G.edgeFinset.card : ℝ) ≤ (g : ℝ)/((g : ℝ)-2) * (Fintype.card V + e) := by
  have hm : ((g : ℝ)-2) * G.edgeFinset.card ≤ (g : ℝ) * (Fintype.card V + (r.eulerGenus : ℝ)) := by
    exact_mod_cast arbitrary_girth_euler_mul_bound V G r g hg3 hg
  have hpos : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  have hgpos : (0 : ℝ) ≤ g := by positivity
  have hh := mul_le_mul_of_nonneg_left he hgpos
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

universe v
theorem copy_girth_edge_bound {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G)
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : Copy H G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (e : ℝ) (he : (r.eulerGenus : ℝ) ≤ e) :
    (H.edgeFinset.card : ℝ) ≤ (g : ℝ)/((g : ℝ)-2) * (Fintype.card W + e) := by
  obtain ⟨s,hs⟩ := r.exists_copy_genus_le f
  have hHg : ∀ (w : W) (c : H.Walk w w), c.IsCycle → g ≤ c.length := by
    intro w c hc
    have hcyc : (c.map f.toHom).IsCycle := hc.map f.injective
    have hh := hg (f w) (c.map f.toHom) hcyc
    exact (Walk.length_map f.toHom c) ▸ hh
  have hs' : (s.eulerGenus : ℝ) ≤ (r.eulerGenus : ℝ) := by exact_mod_cast hs
  exact arbitrary_girth_edge_bound H s g hg3 hHg e (hs'.trans he)

end SimpleGraph.SignedRotation

