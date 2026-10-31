import Mathlib
namespace Paper.LatticeBlock
abbrev Position (q m : ℕ) := Fin q → Fin m
abbrev Vertex (b q m : ℕ) := Fin b × Position q m
abbrev Delta (q : ℕ) := Fin q → ℤ

def Full {q m : ℕ} (r : ℕ) (x : Position q m) : Prop := ∀ i, r ≤ (x i).val ∧ (x i).val+r < m
instance {q m r : ℕ} (x : Position q m) : Decidable (Full r x) := by unfold Full;infer_instance

def difference {q m : ℕ} (x y : Position q m) : Delta q := fun i => ((y i).val:ℤ)-((x i).val:ℤ)
structure Offsets (q s : ℕ) where
  values : Finset (Delta q)
  symmetric : ∀ σ ∈ values, (fun i => -σ i) ∈ values
  nonzero : (fun _ => (0:ℤ)) ∉ values
  bounded : ∀ σ ∈ values, ∀ i, -(s:ℤ) ≤ σ i ∧ σ i ≤ s

structure IsBlockGraph {b q m s : ℕ} (O : Offsets q s) (G : SimpleGraph (Vertex b q m)) : Prop where
  inside : ∀ j x y, G.Adj (j,x) (j,y) ↔ difference x y ∈ O.values
  outside : ∀ j x k y, G.Adj (j,x) (k,y) → j ≠ k → ¬Full s x ∧ ¬Full s y

theorem full_mono {q m r R : ℕ} (h : r ≤ R) {x : Position q m} (hx : Full R x) : Full r x := by
  intro i
  have hh:=hx i
  omega

def shift {q m s : ℕ} (O : Offsets q s) (x : Position q m) (hx : Full s x) (σ : O.values) : Position q m :=
  fun i => ⟨((x i).val+σ.val i).toNat,by
    have hi:=hx i
    have hb:=O.bounded σ.val σ.property i
    omega⟩

theorem shift_difference {q m s : ℕ} (O : Offsets q s) (x : Position q m) (hx : Full s x) (σ : O.values) :
    difference x (shift O x hx σ)=σ.val := by
  funext i
  have hi:=hx i
  have hb:=O.bounded σ.val σ.property i
  dsimp only [difference,shift]
  omega

theorem shift_unique {q m s : ℕ} (O : Offsets q s) (x : Position q m) (hx : Full s x)
    (σ : O.values) (y : Position q m) (hy : difference x y=σ.val) : shift O x hx σ=y := by
  funext i
  apply Fin.ext
  have h1:=congrFun (shift_difference O x hx σ) i
  have h2:=congrFun hy i
  dsimp only [difference] at h1 h2
  omega

theorem shift_full {q m s r : ℕ} (O : Offsets q s) (x : Position q m) (hx : Full ((r+1)*s) x)
    (σ : O.values) : Full (r*s) (shift O x (full_mono (by nlinarith : s ≤ (r+1)*s) hx) σ) := by
  intro i
  have hi:=hx i
  have hb:=O.bounded σ.val σ.property i
  have he:=congrFun (shift_difference O x (full_mono (by nlinarith : s ≤ (r+1)*s) hx) σ) i
  simp only [Nat.add_mul,Nat.one_mul] at hi
  dsimp only [difference] at he
  omega

theorem same_block {b q m s : ℕ} (O : Offsets q s) (G : SimpleGraph (Vertex b q m))
    (H : IsBlockGraph O G) {j k : Fin b} {x y : Position q m} (hx : Full s x)
    (ha : G.Adj (j,x) (k,y)) : j=k := by
  by_contra hn
  exact (H.outside j x k y ha hn).1 hx

noncomputable def fullNeighborEquiv {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (j : Fin b) (x : Position q m) (hx : Full s x) : O.values ≃ G.neighborFinset (j,x) := by
  classical
  let f : O.values → G.neighborFinset (j,x) := fun σ =>
    ⟨(j,shift O x hx σ),(G.mem_neighborFinset _ _).mpr ((H.inside _ _ _).mpr (by
      rw [shift_difference];exact σ.property))⟩
  have hinj : Function.Injective f := by
    intro σ τ he
    apply Subtype.ext
    have h:=congrArg (fun w : G.neighborFinset (j,x) => difference x w.val.2) he
    change difference x (shift O x hx σ)=difference x (shift O x hx τ) at h
    simpa only [shift_difference] using h
  have hsur : Function.Surjective f := by
    intro w
    obtain ⟨⟨k,y⟩,hw⟩:=w
    have ha: G.Adj (j,x) (k,y):=(G.mem_neighborFinset _ _).mp hw
    have hk:=same_block O G H hx ha
    subst k
    let σ : O.values := ⟨difference x y,(H.inside j x y).mp ha⟩
    refine ⟨σ,?_⟩
    apply Subtype.ext
    change (j,shift O x hx σ)=(j,y)
    exact congrArg (fun z : Position q m => (j,z)) (shift_unique O x hx σ y rfl)
  exact Equiv.ofBijective f ⟨hinj,hsur⟩

theorem full_degree {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (j : Fin b) (x : Position q m) (hx : Full s x) : G.degree (j,x)=O.values.card := by
  have h:=Fintype.card_congr (fullNeighborEquiv O G H j x hx)
  simpa only [Fintype.card_coe,SimpleGraph.card_neighborFinset_eq_degree] using h.symm
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.full_degree
