import Paper.Initialization.Pruning.PruningRun
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walks.Counting

/-! The current initializer: distinct successors in nested unions, followed
by two disjoint chains from each final residual vertex. -/
namespace Paper.SuccessorPaths
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
open SevenFoundation

section Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Cancelling equal successors backwards identifies both the starting
vertex and the position in chains whose starts have no active predecessor. -/
theorem iterate_cancel (F : V → V) (A : Finset V)
    (hinj : Set.InjOn F (A : Set V)) {s t : V}
    (hs : ∀ v ∈ A, F v ≠ s) (ht : ∀ v ∈ A, F v ≠ t)
    (n m : ℕ) (hn : ∀ k < n, F^[k] s ∈ A) (hm : ∀ k < m, F^[k] t ∈ A)
    (he : F^[n] s = F^[m] t) : n = m ∧ s = t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact ⟨rfl, he⟩
    | succ m =>
      rw [Function.iterate_zero_apply, Function.iterate_succ_apply'] at he
      exact False.elim (hs _ (hm m (by omega)) he.symm)
  | succ n ih =>
    cases m with
    | zero =>
      rw [Function.iterate_succ_apply', Function.iterate_zero_apply] at he
      exact False.elim (ht _ (hn n (by omega)) he)
    | succ m =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at he
      have he' := hinj (hn n (by omega)) (hm m (by omega)) he
      obtain ⟨hnm, hst⟩ := ih m (fun k hk => hn k (by omega))
        (fun k hk => hm k (by omega)) he'
      exact ⟨congrArg Nat.succ hnm, hst⟩

theorem exists_exit (F : V → V) (A : Finset V)
    (hinj : Set.InjOn F (A : Set V)) (s : V)
    (hs : ∀ v ∈ A, F v ≠ s) : ∃ n, F^[n] s ∉ A := by
  classical
  by_contra hn
  push_neg at hn
  let f : Fin (Fintype.card V + 1) → V := fun i => F^[i.val] s
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (iterate_cancel F A hinj hs hs i.val j.val
      (fun k _ => hn k) (fun k _ => hn k) he).1
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

noncomputable def exitTime (F : V → V) (A : Finset V)
    (hinj : Set.InjOn F (A : Set V)) (s : V)
    (hs : ∀ v ∈ A, F v ≠ s) : ℕ := Nat.find (exists_exit F A hinj s hs)

theorem before_exit (F : V → V) (A : Finset V)
    (hinj : Set.InjOn F (A : Set V)) (s : V)
    (hs : ∀ v ∈ A, F v ≠ s) {k : ℕ} (hk : k < exitTime F A hinj s hs) :
    F^[k] s ∈ A := by
  by_contra hn
  exact Nat.find_min (exists_exit F A hinj s hs) hk hn

theorem at_exit (F : V → V) (A : Finset V)
    (hinj : Set.InjOn F (A : Set V)) (s : V)
    (hs : ∀ v ∈ A, F v ≠ s) : F^[exitTime F A hinj s hs] s ∉ A :=
  Nat.find_spec (exists_exit F A hinj s hs)

theorem exists_walk_iter (G : SimpleGraph V) (F : V → V) (A : Finset V)
    (hedge : ∀ v ∈ A, G.Adj v (F v)) (s : V) (n : ℕ)
    (hpre : ∀ k < n, F^[k] s ∈ A) :
    ∃ w : G.Walk s (F^[n] s), ∀ v, v ∈ w.support ↔ ∃ k ≤ n, F^[k] s = v := by
  induction n with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro v
    simp [eq_comm]
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (fun k hk => hpre k (by omega))
    have ha := hedge _ (hpre n (by omega))
    rw [Function.iterate_succ_apply']
    refine ⟨w.concat ha, ?_⟩
    intro v
    rw [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
    constructor
    · rintro (hv | hv)
      · obtain ⟨k, hk, he⟩ := (hw v).mp hv
        exact ⟨k, by omega, he⟩
      · exact ⟨n+1, le_refl _, by simpa only [Function.iterate_succ_apply'] using hv.symm⟩
    · rintro ⟨k, hk, he⟩
      by_cases hkn : k ≤ n
      · exact Or.inl ((hw v).mpr ⟨k, hkn, he⟩)
      · have hke : k = n+1 := by omega
        subst k
        exact Or.inr (by simpa only [Function.iterate_succ_apply'] using he.symm)

end Orbits

section Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Density alone supplies Hall's condition for at most two requests at
each physical vertex. No acyclic orientation is required. -/
theorem exists_successors (p : ℕ) (hp : 1 ≤ p)
    (hden : MinorDensity.Bound G (p : ℝ)) (A X : Finset V)
    (N : V → Finset V) (hN : ∀ v ∈ A, 3*p ≤ (N v).card)
    (hadj : ∀ v ∈ A, ∀ w ∈ N v, G.Adj v w) :
    ∃ f : (Σ v : A, Fin (if v.val ∈ X then 2 else 1)) → V,
      Function.Injective f ∧ ∀ z, f z ∈ N z.1.val := by
  classical
  let k : A → ℕ := fun v => if v.val ∈ X then 2 else 1
  let M : A → Finset V := fun v => N v.val
  have hall : ∀ Q : Finset (Σ v : A, Fin (k v)),
      Q.card ≤ (Q.biUnion (fun z => M z.1)).card := by
    intro Q
    let P := (Q.image Sigma.fst).image (fun v : A => v.val)
    let W := Q.biUnion (fun z => M z.1)
    have hP : ∀ v ∈ P, v ∈ A ∧ N v ⊆ W := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hu
      refine ⟨u.property, ?_⟩
      intro w hw
      exact Finset.mem_biUnion.mpr ⟨z, hz, by simpa only [M, he] using hw⟩
    have hlo : 3*p*P.card ≤ (G.interedges P W).card := by
      rw [Incidence.card_interedges_eq_sum]
      calc
        _ = ∑ _v ∈ P, 3*p := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun v hv => (hN v (hP v hv).1).trans
          (Finset.card_le_card (fun w hw => Finset.mem_filter.mpr
            ⟨(hP v hv).2 hw, hadj v (hP v hv).1 w hw⟩)))
    have hup := Incidence.card_interedges_le G P W
    have hdu := MinorDensity.induced_bound G hden (P ∪ W)
    have hdi := MinorDensity.induced_bound G hden (P ∩ W)
    have hdu' : G.inducedEdgeCount (P ∪ W) ≤ p*(P ∪ W).card := by
      exact_mod_cast hdu
    have hdi' : G.inducedEdgeCount (P ∩ W) ≤ p*(P ∩ W).card := by
      exact_mod_cast hdi
    have hcards := Finset.card_union_add_card_inter P W
    have hsum : p*(P ∪ W).card + p*(P ∩ W).card = p*(P.card + W.card) := by
      rw [← Nat.mul_add, hcards]
    have hWP : 2*P.card ≤ W.card := by
      have hbound : p * (3 * P.card) ≤ p * (P.card + W.card) := by
        calc
          p * (3 * P.card) = 3*p*P.card := by ac_rfl
          _ ≤ (G.interedges P W).card := hlo
          _ ≤ G.inducedEdgeCount (P ∪ W) + G.inducedEdgeCount (P ∩ W) := hup
          _ ≤ p*(P ∪ W).card + p*(P ∩ W).card := Nat.add_le_add hdu' hdi'
          _ = p*(P.card + W.card) := hsum
      have hcancel := Nat.le_of_mul_le_mul_left hbound (show 0 < p by omega)
      omega
    have hc := CapacitatedHall.copies_card_le k Q
    have hk : (∑ v ∈ Q.image Sigma.fst, k v) ≤ 2*(Q.image Sigma.fst).card := by
      calc
        _ ≤ ∑ _v ∈ Q.image Sigma.fst, 2 := Finset.sum_le_sum (fun v _ => by
          dsimp [k]; split_ifs <;> omega)
        _ = _ := by simp [mul_comm]
    have hPc : P.card = (Q.image Sigma.fst).card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    exact (hc.trans hk).trans (by simpa only [hPc] using hWP)
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun z : Σ v : A, Fin (k v) => M z.1)).mp hall

end Matching

section Chains
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (F : V → V) (A : Finset V) (hinj : Set.InjOn F (A : Set V))
variable (seed : I → V) (hseed : ∀ i v, v ∈ A → F v ≠ seed i)

noncomputable def time (i : I) : ℕ := exitTime F A hinj (seed i) (hseed i)
noncomputable def endpoint (i : I) : V := F^[time F A hinj seed hseed i] (seed i)
noncomputable def segment (i : I) : Finset V :=
  (Finset.range (time F A hinj seed hseed i + 1)).image (fun k => F^[k] (seed i))

theorem segment_mem (i : I) (v : V) : v ∈ segment F A hinj seed hseed i ↔
    ∃ k ≤ time F A hinj seed hseed i, F^[k] (seed i) = v := by
  simp only [segment, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

theorem segment_nonempty (i : I) : (segment F A hinj seed hseed i).Nonempty := by
  exact ⟨seed i, (segment_mem F A hinj seed hseed i _).mpr ⟨0, Nat.zero_le _, rfl⟩⟩

theorem segment_disjoint (hseedi : Function.Injective seed) {i j : I} (hij : i ≠ j) :
    Disjoint (segment F A hinj seed hseed i) (segment F A hinj seed hseed j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨n, hn, he⟩ := (segment_mem F A hinj seed hseed i v).mp hv
  obtain ⟨m, hm, hf⟩ := (segment_mem F A hinj seed hseed j v).mp hw
  have hc := iterate_cancel F A hinj (hseed i) (hseed j) n m
    (fun k hk => before_exit F A hinj (seed i) (hseed i) (by exact lt_of_lt_of_le hk hn))
    (fun k hk => before_exit F A hinj (seed j) (hseed j) (by exact lt_of_lt_of_le hk hm))
    (he.trans hf.symm)
  exact hij (hseedi hc.2)

theorem endpoint_injective (hseedi : Function.Injective seed) :
    Function.Injective (endpoint F A hinj seed hseed) := by
  intro i j he
  have hc := iterate_cancel F A hinj (hseed i) (hseed j)
    (time F A hinj seed hseed i) (time F A hinj seed hseed j)
    (fun k hk => before_exit F A hinj (seed i) (hseed i) hk)
    (fun k hk => before_exit F A hinj (seed j) (hseed j) hk) he
  exact hseedi hc.2

theorem endpoint_outside (i : I) : endpoint F A hinj seed hseed i ∉ A :=
  at_exit F A hinj (seed i) (hseed i)

theorem segment_avoid (B : Finset V) (hAB : Disjoint A B) (i : I)
    (he : endpoint F A hinj seed hseed i ∉ B) :
    Disjoint (segment F A hinj seed hseed i) B := by
  apply Finset.disjoint_left.mpr
  intro v hv hvB
  obtain ⟨n, hn, rfl⟩ := (segment_mem F A hinj seed hseed i v).mp hv
  rcases lt_or_eq_of_le hn with hn | rfl
  · exact Finset.disjoint_left.mp hAB
      (before_exit F A hinj (seed i) (hseed i) hn) hvB
  · exact he hvB

theorem segment_connected (hedge : ∀ v ∈ A, G.Adj v (F v)) (i : I) :
    (G.induce (segment F A hinj seed hseed i : Set V)).Connected := by
  obtain ⟨w, hw⟩ := exists_walk_iter G F A hedge (seed i) (time F A hinj seed hseed i)
    (fun k hk => before_exit F A hinj (seed i) (hseed i) hk)
  have he : (segment F A hinj seed hseed i : Set V) = {v | v ∈ w.support} := by
    ext v
    exact (segment_mem F A hinj seed hseed i v).trans (hw v).symm
  rw [he]
  exact w.connected_induce_support

/-- A chain which leaves a layer visits its prescribed boundary. -/
theorem segment_exit (i : I) (U B : Finset V)
    (hfirst : seed i ∉ U → seed i ∈ B)
    (hstep : ∀ v ∈ A, v ∈ U → F v ∉ U → F v ∈ B)
    (hout : endpoint F A hinj seed hseed i ∉ U) :
    ∃ w ∈ segment F A hinj seed hseed i, w ∈ B := by
  have visit : ∀ n, n ≤ time F A hinj seed hseed i → F^[n] (seed i) ∉ U →
      ∃ k ≤ n, F^[k] (seed i) ∈ B := by
    intro n
    induction n with
    | zero =>
      intro _ hn
      exact ⟨0, le_refl _, hfirst hn⟩
    | succ n ih =>
      intro hn houtn
      by_cases hv : F^[n] (seed i) ∈ U
      · refine ⟨n+1, le_refl _, ?_⟩
        rw [Function.iterate_succ_apply']
        apply hstep _ (before_exit F A hinj (seed i) (hseed i) (by
          change n < time F A hinj seed hseed i; omega)) hv
        simpa only [Function.iterate_succ_apply'] using houtn
      · obtain ⟨k, hk, hb⟩ := ih (by omega) hv
        exact ⟨k, by omega, hb⟩
  obtain ⟨k, hk, hb⟩ := visit _ (le_refl _) hout
  exact ⟨_, (segment_mem F A hinj seed hseed i _).mpr ⟨k, hk, rfl⟩, hb⟩

end Chains

universe u
section Minor
variable {V I : Type u} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def contactGraph (B : I → Finset V) (S : Finset V) : SimpleGraph (I ⊕ S) where
  Adj x y := match x, y with
    | .inl i, .inr s => ∃ v ∈ B i, G.Adj v s.val
    | .inr s, .inl i => ∃ v ∈ B i, G.Adj v s.val
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := ⟨by intro x; cases x <;> exact id⟩

def contactBranch (B : I → Finset V) (S : Finset V) : I ⊕ S → Set V
  | .inl i => B i
  | .inr s => {s.val}

noncomputable def contactModel (B : I → Finset V) (S : Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (havoid : ∀ i, Disjoint (B i) S)
    (hconn : ∀ i, (G.induce (B i : Set V)).Connected) :
    SimpleGraph.MinorModel (contactGraph G B S) G where
  branchSet := contactBranch B S
  nonempty x := by
    cases x with
    | inl i => exact hne i
    | inr s => exact ⟨s.val, rfl⟩
  disjoint x y hxy := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    cases x with
    | inl i =>
      cases y with
      | inl j => exact Finset.disjoint_left.mp (hdis i j (fun he => hxy (congrArg Sum.inl he))) hv hw
      | inr s =>
        change v = s.val at hw
        subst v
        exact Finset.disjoint_left.mp (havoid i) hv s.property
    | inr s =>
      change v = s.val at hv
      subst v
      cases y with
      | inl i => exact Finset.disjoint_left.mp (havoid i) hw s.property
      | inr t => exact hxy (congrArg Sum.inr (Subtype.ext hw))
  connected x := by
    cases x with
    | inl i => exact hconn i
    | inr s =>
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨s.val, rfl⟩, ?_⟩
      intro v
      have he : (⟨s.val, rfl⟩ : {v // v ∈ contactBranch B S (.inr s)}) = v :=
        Subtype.ext v.property.symm
      rw [he]
  adjacent x y hxy := by
    cases x with
    | inl i =>
      cases y with
      | inl j => exact False.elim hxy
      | inr s => obtain ⟨v, hv, ha⟩ := hxy; exact ⟨v, hv, s.val, rfl, ha⟩
    | inr s =>
      cases y with
      | inl i => obtain ⟨v, hv, ha⟩ := hxy; exact ⟨s.val, rfl, v, hv, ha.symm⟩
      | inr t => exact False.elim hxy

theorem connected_sets_count (p T : ℕ) (hden : MinorDensity.Bound G (p : ℝ))
    (B : I → Finset V) (S : Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (havoid : ∀ i, Disjoint (B i) S)
    (hconn : ∀ i, (G.induce (B i : Set V)).Connected)
    (htouch : ∀ i, T ≤ (S.filter (fun s => ∃ v ∈ B i, G.Adj v s)).card) :
    (T : ℝ)*Fintype.card I ≤ (p : ℝ)*(Fintype.card I+S.card) := by
  classical
  let K := contactGraph G B S
  let L : Finset (I ⊕ S) := Finset.univ.image Sum.inl
  let W : Finset (I ⊕ S) := Finset.univ.image Sum.inr
  have hlw : Disjoint L W := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨s, _, he⟩ := Finset.mem_image.mp hw
    cases he
  have hdeg : ∀ v ∈ L, T ≤ (W.filter (K.Adj v)).card := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    let D := S.filter (fun s => ∃ w ∈ B i, G.Adj w s)
    let Ds := D.subtype (fun s => s ∈ S)
    have hc : Ds.card = D.card := StarCounting.subtype_card S D (Finset.filter_subset ..)
    have hsub : Ds.image (Sum.inr : S → I ⊕ S) ⊆ W.filter (K.Adj (.inl i)) := by
      intro w hw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩, ?_⟩
      exact (Finset.mem_filter.mp (Finset.mem_subtype.mp hs)).2
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inr_injective, hc] at hh
    exact (htouch i).trans hh
  have hm : SimpleGraph.IsMinor K G := ⟨contactModel G B S hne hdis havoid hconn⟩
  have hh := CoreMinorCounting.cross_degree_count K
    (MinorDensity.minor_induced_bound G K hden hm) L W hlw T hdeg
  have hLc : L.card = Fintype.card I := by simp [L, Finset.card_image_of_injective, Sum.inl_injective]
  have hWc : W.card = S.card := by simp [W, Finset.card_image_of_injective, Sum.inr_injective]
  rw [hLc, hWc] at hh
  nlinarith

end Minor

section Assignment
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Request (A X : Finset V) := Σ v : A, Fin (if v.val ∈ X then 2 else 1)

def firstRequest (A X : Finset V) (v : V) (hv : v ∈ A) : Request A X :=
  ⟨⟨v, hv⟩, ⟨0, by split_ifs <;> omega⟩⟩

def rootRequest (A X : Finset V) (hXA : X ⊆ A) (i : X × Fin 2) : Request A X :=
  ⟨⟨i.1.val, hXA i.1.property⟩,
    ⟨i.2.val, by simpa only [if_pos i.1.property] using i.2.isLt⟩⟩

theorem rootRequest_injective (A X : Finset V) (hXA : X ⊆ A) :
    Function.Injective (rootRequest A X hXA) := by
  intro i j he
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun z : Request A X => z.1.val) he)
  · exact Fin.ext (congrArg (fun z : Request A X => z.2.val) he)

/-- The tail starts are the two assigned targets of every residual root.
Their active predecessors are disjoint from all root requests. -/
theorem assignment_chains (A X S : Finset V) (hXA : X ⊆ A)
    (N : V → Finset V) (f : Request A X → V) (hf : Function.Injective f)
    (hN : ∀ z, f z ∈ N z.1.val) :
    ∃ (F : V → V) (seed : X × Fin 2 → V),
      Set.InjOn F (↑(A \ (X ∪ S)) : Set V) ∧ Function.Injective seed ∧
      (∀ i v, v ∈ A \ (X ∪ S) → F v ≠ seed i) ∧
      (∀ v ∈ A \ (X ∪ S), F v ∈ N v) ∧
      (∀ i, seed i ∈ N i.1.val) := by
  let B := A \ (X ∪ S)
  let F : V → V := fun v => if hv : v ∈ B then
    f (firstRequest A X v (Finset.mem_sdiff.mp hv).1) else v
  let seed : X × Fin 2 → V := fun i => f (rootRequest A X hXA i)
  have hF : ∀ v (hv : v ∈ B),
      F v = f (firstRequest A X v (Finset.mem_sdiff.mp hv).1) := by
    intro v hv
    simp only [F, dif_pos hv]
  refine ⟨F, seed, ?_, hf.comp (rootRequest_injective A X hXA), ?_, ?_, ?_⟩
  · intro v hv w hw he
    rw [hF v hv, hF w hw] at he
    exact congrArg (fun z : Request A X => z.1.val) (hf he)
  · intro i v hv he
    rw [hF v hv] at he
    have he' := congrArg (fun z : Request A X => z.1.val) (hf he)
    have hvX : v ∈ X := by
      change v = i.1.val at he'
      exact he'.symm ▸ i.1.property
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hvX)
  · intro v hv
    rw [hF v hv]
    exact hN _
  · intro i
    exact hN _

end Assignment

section Layers
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem contacts_from_passes {T : ℕ} (B : Finset V) (D : Fin T → Finset V)
    (S : Finset V) (hDS : ∀ i, D i ⊆ S)
    (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (hBS : Disjoint B S)
    (hvisit : ∀ i, ∃ w ∈ B, w ∈ covered G (D i)) :
    T ≤ (S.filter (fun s => ∃ v ∈ B, G.Adj v s)).card := by
  classical
  have hex : ∀ i, ∃ s ∈ D i, ∃ w ∈ B, G.Adj w s := by
    intro i
    obtain ⟨w, hw, hc⟩ := hvisit i
    obtain ⟨s, hs, hws⟩ := Finset.mem_biUnion.mp hc
    have hne : w ≠ s := by
      intro he
      exact Finset.disjoint_left.mp hBS hw (he.symm ▸ hDS i hs)
    exact ⟨s, hs, w, hw, by
      rcases (mem_closed G w s).mp hws with he | ha
      · exact False.elim (hne he)
      · exact G.symm ha⟩
  choose s hs hw using hex
  let Q := S.filter (fun s => ∃ v ∈ B, G.Adj v s)
  let f : Fin T → Q := fun i => ⟨s i, Finset.mem_filter.mpr ⟨hDS i (hs i), hw i⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    by_contra hn
    have he' : s i = s j := congrArg Subtype.val he
    exact Finset.disjoint_left.mp (hdis i j hn) (hs i) (he'.symm ▸ hs j)
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Abstract nested-layer bound. Its assumptions are local successor
options and the literal coverage of every layer boundary. -/
theorem layer_bound (p : ℕ) (hp : 1 ≤ p) (hden : MinorDensity.Bound G (p : ℝ))
    (A X S : Finset V) (U : Fin (p+1) → Finset V) (D : Fin (p+1) → Finset V)
    (N : V → Finset V) (hXA : X ⊆ A)
    (hUA : ∀ i, U i ⊆ A) (hXU : ∀ i, X ⊆ U i)
    (hDS : ∀ i, D i ⊆ S)
    (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hN : ∀ v ∈ A, 3*p ≤ (N v).card)
    (hadj : ∀ v ∈ A, ∀ w ∈ N v, G.Adj v w)
    (hboundary : ∀ v ∈ A, ∀ w ∈ N v, ∀ i, v ∈ U i → w ∉ U i →
      w ∈ covered G (D i)) :
    X.card ≤ (p+1)*S.card := by
  classical
  obtain ⟨f, hf, hfn⟩ := exists_successors G p hp hden A X N hN hadj
  obtain ⟨F, seed, hinj, hseedinj, hseed, hFn, hsn⟩ :=
    assignment_chains A X S hXA N f hf hfn
  let B := A \ (X ∪ S)
  let E := endpoint F B hinj seed hseed
  let W := segment F B hinj seed hseed
  let good : Finset (X × Fin 2) := Finset.univ.filter (fun i => E i ∉ X ∪ S)
  let bad : Finset (X × Fin 2) := Finset.univ \ good
  have hEi : Function.Injective E := endpoint_injective F B hinj seed hseed hseedinj
  have hbad : bad.card ≤ (X ∪ S).card := by
    have hs : bad.image E ⊆ X ∪ S := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hi' := (Finset.mem_sdiff.mp hi).2
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi'
    have hh := Finset.card_le_card hs
    rwa [Finset.card_image_of_injective _ hEi] at hh
  have htotal : good.card + bad.card = 2*X.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
    simpa only [bad, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_fin, Nat.add_comm, Nat.mul_comm] using hh
  have hXE : X.card ≤ good.card + S.card := by
    have hh := Finset.card_union_le X S
    omega
  have hBW : Disjoint B (X ∪ S) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 hv'
  have hgood : ∀ i : good, E i.val ∉ X ∪ S := fun i => (Finset.mem_filter.mp i.property).2
  have havoid : ∀ i : good, Disjoint (W i.val) S := by
    intro i
    exact (segment_avoid F B hinj seed hseed (X ∪ S) hBW i.val (hgood i)).mono_right
      Finset.subset_union_right
  have hAout : ∀ i : good, E i.val ∉ A := by
    intro i he
    exact endpoint_outside F B hinj seed hseed i.val (Finset.mem_sdiff.mpr ⟨he, hgood i⟩)
  have hvisit : ∀ (i : good) (j : Fin (p+1)), ∃ w ∈ W i.val, w ∈ covered G (D j) := by
    intro i j
    apply segment_exit F B hinj seed hseed i.val (U j) (covered G (D j))
    · intro hsout
      exact hboundary i.val.1.val (hXA i.val.1.property) (seed i.val) (hsn i.val)
        j (hXU j i.val.1.property) hsout
    · intro v hv hvU hout
      exact hboundary v (Finset.mem_sdiff.mp hv).1 (F v) (hFn v hv) j hvU hout
    · exact fun he => hAout i (hUA j he)
  have hconn : ∀ i : good, (G.induce (W i.val : Set V)).Connected := by
    intro i
    exact segment_connected G F B hinj seed hseed
      (fun v hv => hadj v (Finset.mem_sdiff.mp hv).1 (F v) (hFn v hv)) i.val
  have hc := connected_sets_count G p (p+1) hden (fun i : good => W i.val) S
    (fun i => segment_nonempty F B hinj seed hseed i.val)
    (fun i j hn => segment_disjoint F B hinj seed hseed hseedinj
      (fun he => hn (Subtype.ext he))) havoid hconn
    (fun i => contacts_from_passes G (W i.val) D S hDS hdis (havoid i) (hvisit i))
  simp only [Fintype.card_coe, Nat.cast_add, Nat.cast_one] at hc
  have hgoodcard : good.card ≤ p*S.card := by exact_mod_cast (show
      (good.card : ℝ) ≤ (p : ℝ)*S.card by nlinarith)
  nlinarith

end Layers

section Pruning
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The current residual estimate from the actual pruning rules. Hall,
the two terminating chains, their first exits and the minor are all
constructed in the proof; no residual or path certificate is assumed. -/
theorem residual_bound (p : ℕ) (hp : 1 ≤ p)
    (hden : MinorDensity.Bound G (p : ℝ))
    (P : PruningRun.Run G (3*p) (3*p) (p+1)) :
    (P.residual (p+1)).card ≤ (p+1)*(PruningRun.union G P).card := by
  classical
  let C : Fin (p+1) → Finset V := fun i =>
    InitializerPass.candidates G (3*p) (P.residual i.val)
  let U : Fin (p+1) → Finset V := fun i => P.residual (i.val+1) ∪ C i
  let Q : Fin (p+1) → Finset V := fun i => P.residual i.val ∪ C i
  let z : Fin (p+1) := ⟨0, by omega⟩
  let A := U z
  let X := P.residual (p+1)
  let S := PruningRun.union G P
  let D : Fin (p+1) → Finset V := fun i => P.selected i.val
  have hC : ∀ i j : Fin (p+1), i ≤ j → C j ⊆ C i := by
    intro i j hij v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hc := (Finset.mem_filter.mp hv).2
    have hsub : closed G v ∩ P.residual j.val ⊆ closed G v ∩ P.residual i.val :=
      Finset.inter_subset_inter (Finset.Subset.refl _)
        (PruningRun.antitone G P hij (Nat.le_of_lt j.isLt))
    exact lt_of_lt_of_le hc (Finset.card_le_card hsub)
  have hU : ∀ i j : Fin (p+1), i ≤ j → U j ⊆ U i := by
    intro i j hij
    exact Finset.union_subset_union
      (PruningRun.antitone G P (Nat.add_le_add_right hij 1) (by omega)) (hC i j hij)
  have hQ : ∀ i j : Fin (p+1), i ≤ j → Q j ⊆ Q i := by
    intro i j hij
    exact Finset.union_subset_union
      (PruningRun.antitone G P hij (Nat.le_of_lt j.isLt)) (hC i j hij)
  have hXU : ∀ i, X ⊆ U i := by
    intro i v hv
    exact Finset.mem_union_left _
      (PruningRun.antitone G P (by omega : i.val+1 ≤ p+1) (le_refl _) hv)
  have hUA : ∀ i, U i ⊆ A := fun i => hU z i (by exact Nat.zero_le _)
  have hlocal : ∀ (i : Fin (p+1)) v, v ∈ U i →
      3*p ≤ ((G.neighborFinset v) ∩ Q i).card := by
    intro i v hv
    rcases Finset.mem_union.mp hv with hr | hc
    · apply (PruningRun.surviving G P i.val i.isLt hr).trans
      apply Finset.card_le_card
      exact Finset.inter_subset_inter (Finset.Subset.refl _) Finset.subset_union_right
    · apply (InitializerPass.candidate_neighbors G (3*p) (P.residual i.val) hc).trans
      apply Finset.card_le_card
      exact Finset.inter_subset_inter (Finset.Subset.refl _) Finset.subset_union_left
  let N : V → Finset V := fun v => (G.neighborFinset v).filter
    (fun w => ∀ i : Fin (p+1), v ∈ U i → w ∈ Q i)
  have hN : ∀ v ∈ A, 3*p ≤ (N v).card := by
    intro v hv
    let K := Finset.univ.filter (fun i : Fin (p+1) => v ∈ U i)
    have hK : K.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
    let j := K.max' hK
    have hj : v ∈ U j := (Finset.mem_filter.mp (K.max'_mem hK)).2
    apply (hlocal j v hj).trans
    apply Finset.card_le_card
    intro w hw
    have hw' := Finset.mem_inter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨hw'.1, ?_⟩
    intro i hi
    have hij : i ≤ j := Finset.le_max' K i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    exact hQ i j hij hw'.2
  have hDS : ∀ i, D i ⊆ S := by
    intro i v hv
    exact Finset.mem_biUnion.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hv⟩
  apply layer_bound G p hp hden A X S U D N (hXU z) hUA hXU hDS
    (fun i j hn => PruningRun.disjoint G P i.isLt j.isLt
      (fun he => hn (Fin.ext he))) hN
  · intro v _ w hw
    exact (G.mem_neighborFinset v w).mp (Finset.mem_filter.mp hw).1
  · intro v _ w hw i hvU hwU
    have hwQ : w ∈ Q i := (Finset.mem_filter.mp hw).2 i hvU
    have hwR : w ∈ P.residual i.val := by
      rcases Finset.mem_union.mp hwQ with hr | hc
      · exact hr
      · exact False.elim (hwU (Finset.mem_union_right _ hc))
    have hwR' : w ∉ P.residual (i.val+1) := fun hr => hwU (Finset.mem_union_left _ hr)
    by_contra hn
    apply hwR'
    rw [P.step i.val i.isLt]
    exact Finset.mem_sdiff.mpr ⟨hwR, hn⟩

end Pruning

end Paper.SuccessorPaths
