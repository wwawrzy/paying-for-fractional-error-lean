import Paper.Preliminaries.LatticeBlockSelectedCount
namespace Paper.LatticeBlock
open LocalCyclesRamseyInput LocalCyclesRamseyReservoir

def reservoirBound (T m q s : ℕ) : ℕ :=
  ramseyBound 2 ((2*((T+1)*s)+1)^q-1) (m^q)

theorem forced_selection {q m s T b : ℕ} (O : Offsets q s)
    (hm : 2*(T+3)*s+1 ≤ m)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (hT : P.rounds ≤ T) :
    ∃ ids : Vertex b q m → ℕ, Function.Injective ids ∧
      (∀ v, 1 ≤ ids v ∧ ids v ≤ b*m^q) ∧
      (Finset.univ.image ids=Finset.Icc 1 (b*m^q)) ∧
      (network O G H).Compatible G ∧
      (G.IsDominatingSetFinset (selected O G H P ids) →
        (b-reservoirBound T m q s)*(m-2*((T+2)*s))^q ≤ (selected O G H P ids).card) := by
  classical
  let p := (2*((T+1)*s)+1)^q
  have hp : 0 < p := pow_pos (by omega) q
  have hpm : p ≤ m^q := pow_le_pow_left' (by nlinarith : 2*((T+1)*s)+1 ≤ m) q
  obtain ⟨B,hrest,hhom⟩:=exists_blocks (b*m^q) 2 (p-1) (m^q) (by omega)
    (by omega) (windowColor O P ((T+1)*s))
  refine ⟨blockIds B,blockIds_injective B,blockIds_bounds B,?_,compatible O G H,?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hv
      exact Finset.mem_Icc.mpr (blockIds_bounds B w)
    · rw [Finset.card_image_of_injective _ (blockIds_injective B)]
      simp [Vertex,Position]
  · intro hdom
    have hhom' : ∀ j, Homogeneous (windowColor O P ((T+1)*s)) p (B.sets j) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hhom
    have hc:=selected_count O G H P hT hm B hhom' hdom
    have hM : 0 < m^q := pow_pos (by omega) q
    have hk : b-reservoirBound T m q s ≤ B.k := by
      have he:=B.count
      change B.rest.card < reservoirBound T m q s at hrest
      by_contra hh
      have hh' : B.k+reservoirBound T m q s < b := by omega
      have hmul:=Nat.mul_le_mul_right (m^q) (show B.k+reservoirBound T m q s+1 ≤ b by omega)
      have hmul' : reservoirBound T m q s ≤ reservoirBound T m q s*(m^q) :=
        Nat.le_mul_of_pos_right _ hM
      nlinarith
    exact (Nat.mul_le_mul_right ((m-2*((T+2)*s))^q) hk).trans hc

theorem forced_parameters {q m s T : ℕ} (O : Offsets q s)
    (hm : 2*(T+3)*s+1 ≤ m) :
    ∃ ell : ℕ, ∀ (b : ℕ), ell < b →
      ∀ (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
        (P : PortLocal.Program Unit Bool), P.rounds ≤ T →
      ∃ ids : Vertex b q m → ℕ, Function.Injective ids ∧
        (Finset.univ.image ids=Finset.Icc 1 (b*m^q)) ∧
        (network O G H).Compatible G ∧
        (G.IsDominatingSetFinset (selected O G H P ids) →
          (b-ell)*(m-2*((T+2)*s))^q ≤ (selected O G H P ids).card) := by
  refine ⟨reservoirBound T m q s,?_⟩
  intro b hb G inst H P hT
  obtain ⟨ids,hinj,hbounds,hexact,hports,hcount⟩:=forced_selection O hm G H P hT
  exact ⟨ids,hinj,hexact,hports,hcount⟩
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.forced_selection
