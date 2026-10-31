import Paper.Preliminaries.LayeredReach

/-! The finite connecting-set dichotomy: either a small connected set meets
all terminals, or a small cut prevents every remaining component doing so. -/
namespace Paper.ConnectingSets
attribute [local instance] Classical.propDecidable
open LayeredConnector LayeredReach
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem short_projection {n : ℕ} (A : Fin (n + 2) → Finset V)
    {x y : V × Fin (n + 1)} (hx : x ∈ sources A) (hy : y ∈ targets A)
    (p : (graph G A).Walk x y) :
    ∃ T : Finset V, T.card ≤ p.length + 1 ∧ (G.induce (T : Set V)).Connected ∧
      ∀ i, (T ∩ A i).Nonempty := by
  classical
  let T := p.support.toFinset.image Prod.fst
  have hcard : T.card ≤ p.length + 1 := WeakProjection.image_support_card (graph G A) Prod.fst p
  have hconn := WeakProjection.connected_image (graph G A) G Prod.fst (weak_edges G A)
    {z | z ∈ p.support} p.connected_induce_support
  have hs : Prod.fst '' {z | z ∈ p.support} = (T : Set V) := by
    ext v
    simp only [T, Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image, List.mem_toFinset]
  rw [hs] at hconn
  refine ⟨T, hcard, hconn, ?_⟩
  obtain ⟨vx, hvx, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨vy, hvy, rfl⟩ := Finset.mem_image.mp hy
  intro i
  by_cases hi0 : i.val = 0
  · have he : i = 0 := Fin.ext hi0
    refine ⟨vx, Finset.mem_inter.mpr ⟨?_, he ▸ hvx⟩⟩
    exact Finset.mem_image.mpr ⟨(vx, 0), List.mem_toFinset.mpr p.start_mem_support, rfl⟩
  by_cases hilast : i.val = n + 1
  · have he : i = (Fin.last n).succ := Fin.ext hilast
    refine ⟨vy, Finset.mem_inter.mpr ⟨?_, he ▸ hvy⟩⟩
    exact Finset.mem_image.mpr ⟨(vy, Fin.last n), List.mem_toFinset.mpr p.end_mem_support, rfl⟩
  · have hleft : (0 : Fin (n + 1)).val < i.val := by change 0 < i.val; omega
    have hright : i.val ≤ (Fin.last n).val := by change i.val ≤ n; have hh := i.isLt; omega
    obtain ⟨z, hz, hzi⟩ := internal_terminal G A p i hleft hright
    exact ⟨z.1, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨z, List.mem_toFinset.mpr hz, rfl⟩, hzi⟩⟩

theorem dichotomy {n : ℕ} (A : Fin (n + 2) → Finset V) (r : ℕ) (hr : 1 ≤ r) :
    (∃ T : Finset V, T.card ≤ r ∧ (G.induce (T : Set V)).Connected ∧ ∀ i, (T ∩ A i).Nonempty) ∨
      ∃ Z : Finset V, r * Z.card ≤ (n + 1) * Fintype.card V ∧
        ∀ C : Finset V, (G.induce (C : Set V)).Connected → Disjoint C Z →
          ¬ ∀ i, (C ∩ A i).Nonempty := by
  classical
  rcases BfsSeparator.short_walk_or_layer (graph G A) (sources A) (targets A) r hr with hshort | hcut
  · left
    obtain ⟨x, hx, y, hy, p, hp⟩ := hshort
    obtain ⟨T, hT, hc, hm⟩ := short_projection G A hx hy p
    exact ⟨T, hT.trans hp, hc, hm⟩
  · right
    obtain ⟨Z₀, hZ, hcut⟩ := hcut
    let Z := Z₀.image Prod.fst
    refine ⟨Z, ?_, ?_⟩
    · have hc := Nat.mul_le_mul_left r (Finset.card_image_le (s := Z₀) (f := Prod.fst))
      have hh := hc.trans hZ
      simpa only [Fintype.card_prod, Fintype.card_fin, mul_comm] using hh
    · intro C hconn hdis hmeet
      obtain ⟨x, hx, y, hy, p, hp⟩ := connected_walk G A C hconn hmeet
      obtain ⟨z, hz, hzZ⟩ := hcut x hx y hy p
      exact Finset.disjoint_left.mp hdis (hp z hz) (Finset.mem_image.mpr ⟨z, hzZ, rfl⟩)
end Paper.ConnectingSets
