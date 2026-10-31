import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Connectivity.Menger

/-!
# Linked graphs and separators

This module formalizes two notions of linkedness. The historical predicate `IsKLinked` requires pairwise disjoint internal supports, so a terminal of one path may lie on another path. The later predicate `IsKLinkedStrong` requires disjoint full supports and is the book-faithful notion used for connectivity implications.

For `IsKLinked`, the separator bound proved here is conditional: if two disjoint sets `A` and `B` outside a separator `S` each have at least `k` vertices, and `S` separates every vertex of `A` from every vertex of `B`, then `k ≤ |S|`. A `2k` bound is proved only under an additional hypothesis that each path in the chosen linkage has two distinct internal vertices in `S`. The module also develops vertex- and edge-separator criteria, bridge and tree results, and Menger path formulations.
-/

set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false

namespace SimpleGraph

variable {V : Type*}




/-- The internal support of a walk consists of its support vertices other than its endpoints. -/
def Walk.internalSupport {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

@[simp] lemma Walk.mem_internalSupport {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) :
    x ∈ p.internalSupport ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := Iff.rfl


@[simp] lemma Walk.start_not_mem_internalSupport {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : u ∉ p.internalSupport := by
  simp [Walk.internalSupport]

@[simp] lemma Walk.end_not_mem_internalSupport {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : v ∉ p.internalSupport := by
  simp [Walk.internalSupport]


@[simp] lemma Walk.internalSupport_nil {G : SimpleGraph V} {u : V} :
    (Walk.nil : G.Walk u u).internalSupport = (∅ : Set V) := by
  ext x
  simp [Walk.internalSupport]


lemma Walk.internalSupport_subset_support {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : p.internalSupport ⊆ {x | x ∈ p.support} := by
  intro x hx
  exact hx.1




/-- A family of walks is internally disjoint when distinct walks have disjoint internal supports. Endpoints are excluded from these supports. -/
def InternallyDisjoint {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V}
    (paths : ∀ i : Fin k, G.Walk (s i) (t i)) : Prop :=
  Pairwise fun i j => Disjoint (paths i).internalSupport (paths j).internalSupport




/-- Historical internal-support definition of `k`-linkedness. Since only internal supports are compared, a terminal of one path may occur on another path. Use `IsKLinkedStrong` for pairwise disjoint full supports. -/
def IsKLinked (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (s t : Fin k → V), Function.Injective (Sum.elim s t) →
    ∃ (paths : ∀ i : Fin k, G.Walk (s i) (t i)),
      (∀ i, (paths i).IsPath) ∧ InternallyDisjoint paths




theorem IsKLinked.zero (G : SimpleGraph V) : G.IsKLinked 0 := by
  intro s t _
  refine ⟨fun i => i.elim0, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i _ _; exact i.elim0




theorem isKLinked_one_iff {G : SimpleGraph V} :
    G.IsKLinked 1 ↔ ∀ u v : V, u ≠ v → G.Reachable u v := by
  classical
  constructor
  · intro hG u v huv
    
    let s : Fin 1 → V := fun _ => u
    let t : Fin 1 → V := fun _ => v
    have h_inj : Function.Injective (Sum.elim s t) := by
      intro a b hab
      match a, b with
      | Sum.inl ⟨0, _⟩, Sum.inl ⟨0, _⟩ => rfl
      | Sum.inr ⟨0, _⟩, Sum.inr ⟨0, _⟩ => rfl
      | Sum.inl ⟨0, _⟩, Sum.inr ⟨0, _⟩ =>
          simp only [Sum.elim_inl, Sum.elim_inr, s, t] at hab
          exact absurd hab huv
      | Sum.inr ⟨0, _⟩, Sum.inl ⟨0, _⟩ =>
          simp only [Sum.elim_inl, Sum.elim_inr, s, t] at hab
          exact absurd hab.symm huv
    obtain ⟨paths, _, _⟩ := hG s t h_inj
    exact ⟨paths 0⟩
  · intro h s t h_inj
    
    have h_ne : s 0 ≠ t 0 := by
      intro heq
      have hsumeq : Sum.elim s t (Sum.inl 0) = Sum.elim s t (Sum.inr 0) := by
        simp [heq]
      have := h_inj hsumeq
      cases this
    obtain ⟨w⟩ := h (s 0) (t 0) h_ne
    
    let p : G.Walk (s 0) (t 0) := (w.toPath : G.Walk (s 0) (t 0))
    have hp : p.IsPath := (w.toPath).2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have hi : i = 0 := Fin.fin_one_eq_zero i
      rw [hi]
      exact p
    · intro i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      exact hp
    · intro i j hij
      have hi : i = 0 := Fin.fin_one_eq_zero i
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hi; subst hj
      exact absurd rfl hij


theorem IsKLinked.reachable_of_one {G : SimpleGraph V} (hG : G.IsKLinked 1)
    {u v : V} (huv : u ≠ v) : G.Reachable u v :=
  (isKLinked_one_iff.mp hG) u v huv




theorem Walk.exists_internal_mem_of_not_reachable_compl
    {G : SimpleGraph V} {u v : V} {S : Set V}
    (hu : u ∉ S) (hv : v ∉ S)
    (hnr : ¬ (G.induce (Sᶜ : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩)
    (p : G.Walk u v) :
    ∃ x ∈ p.internalSupport, x ∈ S := by
  by_contra h
  push Not at h
  apply hnr
  have hin : ∀ x ∈ p.support, x ∈ (Sᶜ : Set V) := by
    intro x hx hxs
    have hne_u : x ≠ u := fun heq => hu (heq ▸ hxs)
    have hne_v : x ≠ v := fun heq => hv (heq ▸ hxs)
    have hxint : x ∈ p.internalSupport := by
      simp only [Walk.mem_internalSupport]
      exact ⟨hx, hne_u, hne_v⟩
    exact (h x hxint) hxs
  exact ⟨SimpleGraph.Walk.induce _ p hin⟩




theorem card_ge_of_internally_disjoint_meets
    {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V}
    (paths : ∀ i : Fin k, G.Walk (s i) (t i))
    (S : Finset V)
    (hmeets : ∀ i, ∃ x ∈ (paths i).internalSupport, x ∈ S)
    (hdisj : InternallyDisjoint paths) :
    k ≤ S.card := by
  classical
  let f : Fin k → V := fun i => (hmeets i).choose
  have hf_in_supp : ∀ i, f i ∈ (paths i).internalSupport :=
    fun i => (hmeets i).choose_spec.1
  have hf_in_S : ∀ i, f i ∈ S :=
    fun i => (hmeets i).choose_spec.2
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra h
    have hij' : i ≠ j := h
    have hd := hdisj hij'
    have hj_mem : f j ∈ (paths j).internalSupport := hf_in_supp j
    rw [← hij] at hj_mem
    exact hd.le_bot ⟨hf_in_supp i, hj_mem⟩
  have hcard : (Finset.univ : Finset (Fin k)).card ≤ S.card :=
    Finset.card_le_card_of_injOn f (fun i _ => hf_in_S i)
      (fun i _ j _ hij => hinj hij)
  simpa using hcard




/-- If `k`-linkedness supplies paths between two disjoint `k`-vertex sets outside `S`, and no vertex of one set is reachable from the other in `G - S`, then `k ≤ S.card`. -/
theorem IsKLinked.card_separator_ge_of_components_geq
    {G : SimpleGraph V} {k : ℕ} (hG : G.IsKLinked k)
    (S A B : Finset V)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hAB : Disjoint A B)
    (hAk : k ≤ A.card) (hBk : k ≤ B.card)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∀ (ha : a ∉ (S : Set V)) (hb : b ∉ (S : Set V)),
      ¬ (G.induce ((S : Set V)ᶜ)).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    k ≤ S.card := by
  classical
  
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hAk
  obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hBk
  
  have eqA : A' ≃ Fin k := hA'card ▸ A'.equivFin
  have eqB : B' ≃ Fin k := hB'card ▸ B'.equivFin
  
  let s : Fin k → V := fun i => (eqA.symm i).val
  let t : Fin k → V := fun i => (eqB.symm i).val
  
  have hs_in_A : ∀ i, s i ∈ A := fun i => hA'sub (eqA.symm i).property
  have ht_in_B : ∀ i, t i ∈ B := fun i => hB'sub (eqB.symm i).property
  
  have hs_notin_S : ∀ i, s i ∉ S := fun i hsi =>
    Finset.disjoint_left.mp hAS (hs_in_A i) hsi
  have ht_notin_S : ∀ i, t i ∉ S := fun i hti =>
    Finset.disjoint_left.mp hBS (ht_in_B i) hti
  
  have hst_ne : ∀ i j, s i ≠ t j := by
    intro i j heq
    have hsi : s i ∈ A := hs_in_A i
    have htj : t j ∈ B := ht_in_B j
    have : s i ∈ B := heq ▸ htj
    exact Finset.disjoint_left.mp hAB hsi this
  
  have hs_inj : Function.Injective s := by
    intro i j hij
    have h1 : (eqA.symm i).val = (eqA.symm j).val := hij
    have h2 : eqA.symm i = eqA.symm j := Subtype.ext h1
    exact eqA.symm.injective h2
  have ht_inj : Function.Injective t := by
    intro i j hij
    have h1 : (eqB.symm i).val = (eqB.symm j).val := hij
    have h2 : eqB.symm i = eqB.symm j := Subtype.ext h1
    exact eqB.symm.injective h2
  
  have h_inj : Function.Injective (Sum.elim s t) :=
    Function.Injective.sumElim hs_inj ht_inj hst_ne
  
  obtain ⟨paths, _, hdisj⟩ := hG s t h_inj
  
  have hmeets : ∀ i, ∃ x ∈ (paths i).internalSupport, x ∈ S := by
    intro i
    have hsi_notin : (s i : V) ∉ (S : Set V) := by
      simp only [Finset.mem_coe]
      exact hs_notin_S i
    have hti_notin : (t i : V) ∉ (S : Set V) := by
      simp only [Finset.mem_coe]
      exact ht_notin_S i
    have hnr := hsep (s i) (hs_in_A i) (t i) (ht_in_B i) hsi_notin hti_notin
    have hres := Walk.exists_internal_mem_of_not_reachable_compl
      hsi_notin hti_notin hnr (paths i)
    obtain ⟨x, hxi, hxS⟩ := hres
    exact ⟨x, hxi, hxS⟩
  exact card_ge_of_internally_disjoint_meets paths S hmeets hdisj






def IsSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ¬ (G.induce ((S : Set V)ᶜ)).Connected


structure IsMinSeparator (G : SimpleGraph V) (S : Finset V) : Prop where
  
  isSeparator : G.IsSeparator S
  
  minimal : ∀ T : Finset V, T ⊂ S → ¬ G.IsSeparator T


theorem IsMinSeparator.toIsSeparator {G : SimpleGraph V} {S : Finset V}
    (hmin : G.IsMinSeparator S) : G.IsSeparator S :=
  hmin.isSeparator


theorem exists_minSeparator_subset_of_separator
    {G : SimpleGraph V} {S : Finset V} (hS : G.IsSeparator S) :
    ∃ T : Finset V, T ⊆ S ∧ G.IsMinSeparator T := by
  classical
  
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hmin : ∀ T : Finset V, T ⊂ S → ¬ G.IsSeparator T
    · exact ⟨S, subset_refl S, ⟨hS, hmin⟩⟩
    · push Not at hmin
      obtain ⟨T, hTsub, hTsep⟩ := hmin
      have hTcard : T.card < S.card := Finset.card_lt_card hTsub
      rw [hn] at hTcard
      obtain ⟨T', hT'sub, hT'min⟩ := ih T.card hTcard hTsep rfl
      exact ⟨T', hT'sub.trans hTsub.subset, hT'min⟩




theorem IsMinSeparator.exists_neighbor_in_component
    {G : SimpleGraph V} [DecidableEq V]
    {S : Finset V} (hmin : G.IsMinSeparator S)
    {s : V} (hs : s ∈ S)
    (C : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) :
    ∃ c : V, ∃ (hcS : c ∉ (S : Set V)),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨c, hcS⟩ = C ∧ G.Adj s c := by
  classical
  
  by_contra hcontra
  push Not at hcontra
  
  
  set T : Finset V := S.erase s with hT_def
  have hTsubS : T ⊂ S := Finset.erase_ssubset hs
  
  apply hmin.minimal T hTsubS
  
  intro hTconn
  
  
  
  
  
  
  
  have hSsep : ¬ (G.induce ((S : Set V)ᶜ)).Connected := hmin.isSeparator
  
  
  
  obtain ⟨⟨c0, hc0_notS⟩, hc0_eq⟩ : ∃ x : ((S : Set V)ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C := C.exists_rep
  
  
  have hSc_nonempty : Nonempty ((S : Set V)ᶜ : Set V) := ⟨⟨c0, hc0_notS⟩⟩
  have hNotPre : ¬ (G.induce ((S : Set V)ᶜ)).Preconnected := by
    intro hpre
    exact hSsep ⟨hpre⟩
  
  unfold SimpleGraph.Preconnected at hNotPre
  push Not at hNotPre
  obtain ⟨x, y, hxy⟩ := hNotPre
  
  
  
  have hxC_or_yC : (G.induce ((S : Set V)ᶜ)).connectedComponentMk x ≠ C ∨
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk y ≠ C := by
    by_contra hboth
    push Not at hboth
    obtain ⟨hxC, hyC⟩ := hboth
    apply hxy
    have : (G.induce ((S : Set V)ᶜ)).connectedComponentMk x =
        (G.induce ((S : Set V)ᶜ)).connectedComponentMk y := hxC.trans hyC.symm
    exact (SimpleGraph.ConnectedComponent.eq).mp this
  
  obtain ⟨⟨d, hd_notS⟩, hd_compne⟩ :
      ∃ z : ((S : Set V)ᶜ : Set V),
        (G.induce ((S : Set V)ᶜ)).connectedComponentMk z ≠ C := by
    rcases hxC_or_yC with hx | hy
    · exact ⟨x, hx⟩
    · exact ⟨y, hy⟩
  
  
  have hc0_notT : (c0 : V) ∉ (T : Set V) := by
    intro hin
    have : c0 ∈ T := hin
    have : c0 ∈ S := Finset.mem_of_subset hTsubS.subset this
    exact hc0_notS this
  have hd_notT : (d : V) ∉ (T : Set V) := by
    intro hin
    have : d ∈ T := hin
    have : d ∈ S := Finset.mem_of_subset hTsubS.subset this
    exact hd_notS this
  have hreach : (G.induce ((T : Set V)ᶜ)).Reachable
      ⟨c0, hc0_notT⟩ ⟨d, hd_notT⟩ := hTconn.preconnected _ _
  
  
  
  
  
  
  
  
  
  obtain ⟨w⟩ := hreach
  
  
  
  
  suffices key : ∀ {u v : ((T : Set V)ᶜ : Set V)}
      (_ : (G.induce ((T : Set V)ᶜ)).Walk u v)
      (hu_inSc : (u : V) ∉ (S : Set V)),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨u.val, hu_inSc⟩ = C →
      ∃ hv_inSc : (v : V) ∉ (S : Set V),
        (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨v.val, hv_inSc⟩ = C by
    obtain ⟨hd_inSc', hd_inC⟩ := key w hc0_notS hc0_eq
    exact hd_compne hd_inC
  intro u v w
  induction w with
  | nil =>
      intro hu_inSc hu_inC
      refine ⟨hu_inSc, ?_⟩
      exact hu_inC
  | @cons u x v hadj w' ih =>
      intro hu_inSc hu_inC
      
      have hadj_G : G.Adj u.val x.val := hadj
      
      by_cases hxS : (x : V) ∈ (S : Set V)
      · 
        have hx_notT : (x : V) ∉ (T : Set V) := x.property
        have hx_in_S : (x : V) ∈ S := hxS
        have hx_eq_s : (x : V) = s := by
          by_contra hne
          apply hx_notT
          exact Finset.mem_erase.mpr ⟨hne, hx_in_S⟩
        
        
        exfalso
        have hadj_us : G.Adj u.val s := hx_eq_s ▸ hadj_G
        have hsu : G.Adj s u.val := hadj_us.symm
        exact hcontra u.val hu_inSc hu_inC hsu
      · 
        have hadj_Sc : (G.induce ((S : Set V)ᶜ)).Adj ⟨u.val, hu_inSc⟩ ⟨x.val, hxS⟩ :=
          hadj_G
        
        have hx_inC : (G.induce ((S : Set V)ᶜ)).connectedComponentMk
            ⟨x.val, hxS⟩ = C := by
          rw [← hu_inC]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj_Sc.symm)
        exact ih hxS hx_inC


theorem IsMinSeparator.exists_neighbor_in_each_component
    {G : SimpleGraph V} [DecidableEq V]
    {S : Finset V} (hmin : G.IsMinSeparator S)
    (s : V) (hs : s ∈ S)
    (C : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) :
    ∃ c : V, ∃ (hcS : c ∉ (S : Set V)),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨c, hcS⟩ = C ∧ G.Adj s c :=
  hmin.exists_neighbor_in_component hs C




theorem IsSeparator.exists_two_distinct_components
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {S : Finset V} (hS : G.IsSeparator S)
    (h_compl_nonempty : (S : Set V)ᶜ.Nonempty) :
    ∃ C₁ C₂ : (G.induce ((S : Set V)ᶜ)).ConnectedComponent, C₁ ≠ C₂ := by
  classical
  
  unfold IsSeparator at hS
  
  obtain ⟨a, ha⟩ := h_compl_nonempty
  have hNonempty : Nonempty ((S : Set V)ᶜ : Set V) := ⟨⟨a, ha⟩⟩
  
  have hNotPre : ¬ (G.induce ((S : Set V)ᶜ)).Preconnected := by
    intro hpre
    exact hS ⟨hpre⟩
  
  unfold SimpleGraph.Preconnected at hNotPre
  push Not at hNotPre
  obtain ⟨x, y, hxy⟩ := hNotPre
  
  refine ⟨(G.induce ((S : Set V)ᶜ)).connectedComponentMk x,
          (G.induce ((S : Set V)ᶜ)).connectedComponentMk y, ?_⟩
  intro heq
  exact hxy ((SimpleGraph.ConnectedComponent.eq).mp heq)


theorem IsMinSeparator.exists_two_distinct_components
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {S : Finset V} (hmin : G.IsMinSeparator S)
    (h_compl_nonempty : (S : Set V)ᶜ.Nonempty) :
    ∃ C₁ C₂ : (G.induce ((S : Set V)ᶜ)).ConnectedComponent, C₁ ≠ C₂ :=
  hmin.toIsSeparator.exists_two_distinct_components h_compl_nonempty




theorem IsMinSeparator.exists_two_distinct_neighbors_in_diff_components
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {S : Finset V} (hmin : G.IsMinSeparator S)
    (h_compl_nonempty : (S : Set V)ᶜ.Nonempty)
    (s : V) (hs : s ∈ S) :
    ∃ a b : V, ∃ (ha : a ∉ (S : Set V)) (hb : b ∉ (S : Set V)),
      G.Adj s a ∧ G.Adj s b ∧
      ¬ (G.induce ((S : Set V)ᶜ)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  
  obtain ⟨C₁, C₂, hC_ne⟩ := hmin.exists_two_distinct_components h_compl_nonempty
  
  obtain ⟨a, ha_notS, ha_inC, hsa⟩ :=
    hmin.exists_neighbor_in_each_component s hs C₁
  
  obtain ⟨b, hb_notS, hb_inC, hsb⟩ :=
    hmin.exists_neighbor_in_each_component s hs C₂
  refine ⟨a, b, ha_notS, hb_notS, hsa, hsb, ?_⟩
  
  intro hreach
  
  have hcmk_eq : (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨a, ha_notS⟩ =
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk ⟨b, hb_notS⟩ :=
    (SimpleGraph.ConnectedComponent.eq).mpr hreach
  
  rw [ha_inC, hb_inC] at hcmk_eq
  exact hC_ne hcmk_eq




def IsSeparatingVertex (G : SimpleGraph V) (v : V) : Prop :=
  G.IsSeparator {v}


theorem isSeparatingVertex_iff_isSeparator_singleton {G : SimpleGraph V} {v : V} :
    G.IsSeparatingVertex v ↔ G.IsSeparator {v} := Iff.rfl


theorem connected_induce_univ_iff (G : SimpleGraph V) :
    (G.induce Set.univ).Connected ↔ G.Connected := by
  classical
  constructor
  · intro h
    
    have hsurj : Function.Surjective (G.induceUnivIso : G.induce Set.univ →g G) :=
      G.induceUnivIso.toEquiv.surjective
    exact h.map _ hsurj
  · intro h
    have hsurj : Function.Surjective
        (G.induceUnivIso.symm : G →g G.induce Set.univ) :=
      G.induceUnivIso.symm.toEquiv.surjective
    exact h.map _ hsurj


private theorem compl_empty_eq_univ_finset {V : Type*} :
    ((∅ : Finset V) : Set V)ᶜ = Set.univ := by
  simp


theorem IsSeparatingVertex.isMinSeparator
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    {v : V} (hG : G.Connected) (hv : G.IsSeparatingVertex v) :
    G.IsMinSeparator {v} := by
  classical
  refine ⟨hv, fun T hT => ?_⟩
  
  have hT_empty : T = ∅ := Finset.ssubset_singleton_iff.mp hT
  subst hT_empty
  
  intro hsep
  unfold IsSeparator at hsep
  
  rw [compl_empty_eq_univ_finset] at hsep
  
  exact hsep ((connected_induce_univ_iff G).mpr hG)






/-- Pairwise internally disjoint paths contribute at least `2 * k` distinct vertices to `S` when each path has two distinct internal vertices in `S`. -/
theorem card_ge_2k_of_internally_disjoint_two_meets
    {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V}
    (paths : ∀ i : Fin k, G.Walk (s i) (t i))
    (S : Finset V)
    (h_two : ∀ i, ∃ x ∈ (paths i).internalSupport, ∃ y ∈ (paths i).internalSupport,
                   x ∈ S ∧ y ∈ S ∧ x ≠ y)
    (hdisj : InternallyDisjoint paths) :
    2 * k ≤ S.card := by
  classical
  
  let xy : Fin k → V × V := fun i =>
    let h := h_two i
    (h.choose, h.choose_spec.2.choose)
  have hx_in_supp : ∀ i, (xy i).1 ∈ (paths i).internalSupport := fun i =>
    (h_two i).choose_spec.1
  have hy_in_supp : ∀ i, (xy i).2 ∈ (paths i).internalSupport := fun i =>
    (h_two i).choose_spec.2.choose_spec.1
  have hx_in_S : ∀ i, (xy i).1 ∈ S := fun i =>
    (h_two i).choose_spec.2.choose_spec.2.1
  have hy_in_S : ∀ i, (xy i).2 ∈ S := fun i =>
    (h_two i).choose_spec.2.choose_spec.2.2.1
  have hxy_ne : ∀ i, (xy i).1 ≠ (xy i).2 := fun i =>
    (h_two i).choose_spec.2.choose_spec.2.2.2
  
  let g : Fin k × Bool → V := fun p => if p.2 then (xy p.1).2 else (xy p.1).1
  have hg_in_S : ∀ p : Fin k × Bool, g p ∈ S := by
    intro p
    by_cases hb : p.2
    · simp [g, hb, hy_in_S]
    · simp [g, hb, hx_in_S]
  
  have hg_inj : Function.Injective g := by
    rintro ⟨i, bi⟩ ⟨j, bj⟩ heq
    have heq' : g (i, bi) = g (j, bj) := heq
    
    by_cases hij : i = j
    · subst hij
      
      by_cases hbi : bi
      · by_cases hbj : bj
        · simp [hbi, hbj]
        · 
          simp only [g, hbi, hbj] at heq
          exact absurd heq.symm (hxy_ne i)
      · by_cases hbj : bj
        · simp only [g, hbi, hbj] at heq
          exact absurd heq (hxy_ne i)
        · simp [hbi, hbj]
    · 
      exfalso
      have hd := hdisj hij
      have hgi : g (i, bi) ∈ (paths i).internalSupport := by
        by_cases hbi : bi
        · simp only [g, hbi, if_true]; exact hy_in_supp i
        · simp only [g, hbi]; exact hx_in_supp i
      have hgj : g (j, bj) ∈ (paths j).internalSupport := by
        by_cases hbj : bj
        · simp only [g, hbj, if_true]; exact hy_in_supp j
        · simp only [g, hbj]; exact hx_in_supp j
      have hgi' : g (j, bj) ∈ (paths i).internalSupport := heq' ▸ hgi
      exact hd.le_bot ⟨hgi', hgj⟩
  
  have hcard_prod : (Finset.univ : Finset (Fin k × Bool)).card = 2 * k := by
    rw [Finset.card_univ]
    simp [Nat.mul_comm]
  
  have hle : (Finset.univ : Finset (Fin k × Bool)).card ≤ S.card :=
    Finset.card_le_card_of_injOn g (fun p _ => hg_in_S p)
      (fun p _ q _ hpq => hg_inj hpq)
  rw [hcard_prod] at hle
  exact hle


/-- Under the additional `h_two_meets` hypothesis for the selected linkage, the separator has at least `2 * k` vertices. Minimality of `S` is an explicit hypothesis; the extra path-intersection condition is not derived here. -/
theorem IsKLinked.card_separator_ge_two_k_of_components_geq
    {G : SimpleGraph V} {k : ℕ} (hG : G.IsKLinked k)
    (S A B : Finset V) (hmin : G.IsMinSeparator S)
    (hAS : Disjoint A S) (hBS : Disjoint B S) (hAB : Disjoint A B)
    (hAk : k ≤ A.card) (hBk : k ≤ B.card)
    (_hsep : ∀ a ∈ A, ∀ b ∈ B, ∀ (ha : a ∉ (S : Set V)) (hb : b ∉ (S : Set V)),
      ¬ (G.induce ((S : Set V)ᶜ)).Reachable ⟨a, ha⟩ ⟨b, hb⟩)
    
    (h_two_meets : ∀ (s_fn t_fn : Fin k → V),
      Function.Injective (Sum.elim s_fn t_fn) →
      (∀ i, s_fn i ∈ A) → (∀ i, t_fn i ∈ B) →
      ∀ (paths : ∀ i : Fin k, G.Walk (s_fn i) (t_fn i)),
      (∀ i, (paths i).IsPath) → InternallyDisjoint paths →
      ∀ i, ∃ x ∈ (paths i).internalSupport, ∃ y ∈ (paths i).internalSupport,
        x ∈ S ∧ y ∈ S ∧ x ≠ y) :
    2 * k ≤ S.card := by
  classical
  
  
  have _ := hmin
  
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hAk
  obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hBk
  have eqA : A' ≃ Fin k := hA'card ▸ A'.equivFin
  have eqB : B' ≃ Fin k := hB'card ▸ B'.equivFin
  let s : Fin k → V := fun i => (eqA.symm i).val
  let t : Fin k → V := fun i => (eqB.symm i).val
  have hs_in_A : ∀ i, s i ∈ A := fun i => hA'sub (eqA.symm i).property
  have ht_in_B : ∀ i, t i ∈ B := fun i => hB'sub (eqB.symm i).property
  have hs_notin_S : ∀ i, s i ∉ S := fun i hsi =>
    Finset.disjoint_left.mp hAS (hs_in_A i) hsi
  have ht_notin_S : ∀ i, t i ∉ S := fun i hti =>
    Finset.disjoint_left.mp hBS (ht_in_B i) hti
  have hst_ne : ∀ i j, s i ≠ t j := by
    intro i j heq
    have hsi : s i ∈ A := hs_in_A i
    have htj : t j ∈ B := ht_in_B j
    have : s i ∈ B := heq ▸ htj
    exact Finset.disjoint_left.mp hAB hsi this
  have hs_inj : Function.Injective s := by
    intro i j hij
    have h1 : (eqA.symm i).val = (eqA.symm j).val := hij
    have h2 : eqA.symm i = eqA.symm j := Subtype.ext h1
    exact eqA.symm.injective h2
  have ht_inj : Function.Injective t := by
    intro i j hij
    have h1 : (eqB.symm i).val = (eqB.symm j).val := hij
    have h2 : eqB.symm i = eqB.symm j := Subtype.ext h1
    exact eqB.symm.injective h2
  have h_inj : Function.Injective (Sum.elim s t) :=
    Function.Injective.sumElim hs_inj ht_inj hst_ne
  
  obtain ⟨paths, hpaths_IsPath, hdisj⟩ := hG s t h_inj
  
  have h_two : ∀ i, ∃ x ∈ (paths i).internalSupport,
                    ∃ y ∈ (paths i).internalSupport,
                      x ∈ S ∧ y ∈ S ∧ x ≠ y :=
    h_two_meets s t h_inj hs_in_A ht_in_B paths hpaths_IsPath hdisj
  
  exact card_ge_2k_of_internally_disjoint_two_meets paths S h_two hdisj



section MinSeparatorConnectivity

variable [Fintype V] [DecidableEq V]


private theorem set_compl_finset_eq_univ_sdiff_local
    (S : Finset V) :
    ((↑S : Set V))ᶜ = (↑(Finset.univ \ S) : Set V) := by
  ext x
  simp


theorem not_isKConnected_extract
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hcard : k + 1 ≤ Fintype.card V)
    (h : ¬ G.IsKConnected k) :
    ∃ S : Finset V, S.card < k ∧ G.IsSeparator S := by
  classical
  
  
  have hk_pos : 0 < k := by
    by_contra hk0
    push Not at hk0
    interval_cases k
    
    exact h (Nat.zero_le _)
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    omega
  
  unfold IsKConnected at h
  
  by_contra hAll
  
  
  have hkvc : G.IsVertexConnected k := by
    refine ⟨by omega, fun S hS => ?_⟩
    by_contra hC
    apply hAll
    refine ⟨S, hS, ?_⟩
    
    
    
    change ¬ (G.induce ((↑S : Set V))ᶜ).Connected
    rwa [set_compl_finset_eq_univ_sdiff_local]
  
  have hkle : k ≤ G.vertexConnectivity :=
    le_vertexConnectivity_of_isVertexConnected G hkvc
  exact h hkle


theorem IsKConnected.not_iff_exists_minSeparator_lt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hcard : k + 1 ≤ Fintype.card V) :
    ¬ G.IsKConnected k ↔ ∃ S : Finset V, S.card < k ∧ G.IsMinSeparator S := by
  classical
  
  
  
  constructor
  · 
    intro hnot
    obtain ⟨S, hScard, hSsep⟩ := G.not_isKConnected_extract hcard hnot
    obtain ⟨T, hTsubS, hTmin⟩ := exists_minSeparator_subset_of_separator hSsep
    refine ⟨T, ?_, hTmin⟩
    exact lt_of_le_of_lt (Finset.card_le_card hTsubS) hScard
  · 
    rintro ⟨S, hScard, hSmin⟩ hKConn
    
    haveI : Nontrivial V := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      have : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hScard
      omega
    
    have hvc : G.IsVertexConnected k := hKConn.isVertexConnected
    
    have hConn : (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected :=
      hvc.2 S hScard
    
    have hSep : ¬ (G.induce ((↑S : Set V))ᶜ).Connected := hSmin.isSeparator
    apply hSep
    rwa [set_compl_finset_eq_univ_sdiff_local]


theorem IsKConnected.iff_all_minSeparator_card_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hcard : k + 1 ≤ Fintype.card V) :
    G.IsKConnected k ↔ ∀ S : Finset V, G.IsMinSeparator S → k ≤ S.card := by
  classical
  
  
  constructor
  · 
    intro hKConn S hSmin
    by_contra hScard
    push Not at hScard
    
    
    have hnot : ¬ G.IsKConnected k :=
      (IsKConnected.not_iff_exists_minSeparator_lt G hcard).mpr ⟨S, hScard, hSmin⟩
    exact hnot hKConn
  · 
    intro hAll
    by_contra hnot
    
    obtain ⟨S, hScard, hSmin⟩ :=
      (IsKConnected.not_iff_exists_minSeparator_lt G hcard).mp hnot
    exact absurd (hAll S hSmin) (Nat.not_le_of_lt hScard)

end MinSeparatorConnectivity



section IsKLinkedMonotone

variable [Fintype V] [DecidableEq V]


theorem IsKLinked.pred {G : SimpleGraph V} {k : ℕ}
    (hcard : 2 * (k + 1) ≤ Fintype.card V)
    (hG : G.IsKLinked (k + 1)) : G.IsKLinked k := by
  classical
  intro s' t' hinj'
  
  let img : Finset V := (Finset.univ : Finset (Fin k)).image s' ∪
                       (Finset.univ : Finset (Fin k)).image t'
  
  have hs'_inj : Function.Injective s' := by
    intro i j hij
    have : Sum.elim s' t' (Sum.inl i) = Sum.elim s' t' (Sum.inl j) := by
      simp [hij]
    have heq := hinj' this
    cases heq; rfl
  have ht'_inj : Function.Injective t' := by
    intro i j hij
    have : Sum.elim s' t' (Sum.inr i) = Sum.elim s' t' (Sum.inr j) := by
      simp [hij]
    have heq := hinj' this
    cases heq; rfl
  have hst'_disj : ∀ i j : Fin k, s' i ≠ t' j := by
    intro i j heq
    have : Sum.elim s' t' (Sum.inl i) = Sum.elim s' t' (Sum.inr j) := by
      simp [heq]
    exact Sum.inl_ne_inr (hinj' this)
  
  have him_s : ((Finset.univ : Finset (Fin k)).image s').card = k := by
    rw [Finset.card_image_of_injective _ hs'_inj]
    simp
  have him_t : ((Finset.univ : Finset (Fin k)).image t').card = k := by
    rw [Finset.card_image_of_injective _ ht'_inj]
    simp
  have him_disj : Disjoint ((Finset.univ : Finset (Fin k)).image s')
                          ((Finset.univ : Finset (Fin k)).image t') := by
    rw [Finset.disjoint_left]
    rintro x hxs hxt
    rcases Finset.mem_image.mp hxs with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hxt with ⟨j, _, hxj⟩
    exact hst'_disj i j hxj.symm
  have himg_card : img.card = 2 * k := by
    change (((Finset.univ : Finset (Fin k)).image s') ∪
          ((Finset.univ : Finset (Fin k)).image t')).card = 2 * k
    rw [Finset.card_union_of_disjoint him_disj, him_s, him_t]
    ring
  
  have hcompl_card : 2 ≤ (Finset.univ \ img).card := by
    rw [Finset.card_univ_diff, himg_card]
    omega
  
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hcompl_card
  
  have hWne : W.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨u, hu_mem⟩ := hWne
  have hWerase_ne : (W.erase u).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hu_mem]
    omega
  obtain ⟨v, hv_mem⟩ := hWerase_ne
  have huv_ne : u ≠ v := (Finset.mem_erase.mp hv_mem).1.symm
  have hv_in_W : v ∈ W := (Finset.mem_erase.mp hv_mem).2
  have hu_notin_img : u ∉ img := by
    have : u ∈ Finset.univ \ img := hWsub hu_mem
    exact (Finset.mem_sdiff.mp this).2
  have hv_notin_img : v ∉ img := by
    have : v ∈ Finset.univ \ img := hWsub hv_in_W
    exact (Finset.mem_sdiff.mp this).2
  
  have hu_ne_s' : ∀ i, u ≠ s' i := by
    intro i heq
    apply hu_notin_img
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, by simp, heq.symm⟩))
  have hu_ne_t' : ∀ i, u ≠ t' i := by
    intro i heq
    apply hu_notin_img
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, by simp, heq.symm⟩))
  have hv_ne_s' : ∀ i, v ≠ s' i := by
    intro i heq
    apply hv_notin_img
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, by simp, heq.symm⟩))
  have hv_ne_t' : ∀ i, v ≠ t' i := by
    intro i heq
    apply hv_notin_img
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, by simp, heq.symm⟩))
  
  let s : Fin (k + 1) → V := fun i =>
    if h : i.val < k then s' ⟨i.val, h⟩ else u
  let t : Fin (k + 1) → V := fun i =>
    if h : i.val < k then t' ⟨i.val, h⟩ else v
  
  have hs_emb : ∀ (i : Fin k), s ⟨i.val, by omega⟩ = s' i := by
    intro i; simp [s, i.isLt]
  have ht_emb : ∀ (i : Fin k), t ⟨i.val, by omega⟩ = t' i := by
    intro i; simp [t, i.isLt]
  have hs_last : s ⟨k, Nat.lt_succ_self k⟩ = u := by simp [s]
  have ht_last : t ⟨k, Nat.lt_succ_self k⟩ = v := by simp [t]
  
  have hinj : Function.Injective (Sum.elim s t) := by
    intro a b hab
    
    rcases a with i | i <;> rcases b with j | j <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · 
      by_cases hi : i.val < k
      · by_cases hj : j.val < k
        · simp only [s, dif_pos hi, dif_pos hj] at hab
          have hh := hs'_inj hab
          have hij_val : i.val = j.val := by
            have := Fin.mk.inj_iff.mp hh
            exact this
          have : i = j := Fin.ext hij_val
          rw [this]
        · 
          have hjeq : j.val = k := by omega
          simp only [s, dif_pos hi, dif_neg hj] at hab
          exact absurd hab.symm (hu_ne_s' ⟨i.val, hi⟩)
      · 
        have hieq : i.val = k := by omega
        by_cases hj : j.val < k
        · simp only [s, dif_neg hi, dif_pos hj] at hab
          exact absurd hab (hu_ne_s' ⟨j.val, hj⟩)
        · 
          have hjeq : j.val = k := by omega
          have : i = j := Fin.ext (by omega)
          rw [this]
    · 
      by_cases hi : i.val < k
      · by_cases hj : j.val < k
        · simp only [s, t, dif_pos hi, dif_pos hj] at hab
          exact absurd hab (hst'_disj _ _)
        · simp only [s, t, dif_pos hi, dif_neg hj] at hab
          exact absurd hab.symm (hv_ne_s' ⟨i.val, hi⟩)
      · by_cases hj : j.val < k
        · simp only [s, t, dif_neg hi, dif_pos hj] at hab
          exact absurd hab (hu_ne_t' ⟨j.val, hj⟩)
        · simp only [s, t, dif_neg hi, dif_neg hj] at hab
          exact absurd hab huv_ne
    · 
      by_cases hi : i.val < k
      · by_cases hj : j.val < k
        · simp only [s, t, dif_pos hi, dif_pos hj] at hab
          exact absurd hab.symm (hst'_disj _ _)
        · simp only [s, t, dif_pos hi, dif_neg hj] at hab
          exact absurd hab.symm (hu_ne_t' ⟨i.val, hi⟩)
      · by_cases hj : j.val < k
        · simp only [s, t, dif_neg hi, dif_pos hj] at hab
          exact absurd hab (hv_ne_s' ⟨j.val, hj⟩)
        · simp only [s, t, dif_neg hi, dif_neg hj] at hab
          exact absurd hab.symm huv_ne
    · 
      by_cases hi : i.val < k
      · by_cases hj : j.val < k
        · simp only [t, dif_pos hi, dif_pos hj] at hab
          have hh := ht'_inj hab
          have hij_val : i.val = j.val := Fin.mk.inj_iff.mp hh
          have : i = j := Fin.ext hij_val
          rw [this]
        · simp only [t, dif_pos hi, dif_neg hj] at hab
          exact absurd hab.symm (hv_ne_t' ⟨i.val, hi⟩)
      · by_cases hj : j.val < k
        · simp only [t, dif_neg hi, dif_pos hj] at hab
          exact absurd hab (hv_ne_t' ⟨j.val, hj⟩)
        · have : i = j := Fin.ext (by omega)
          rw [this]
  
  obtain ⟨paths, hIsPath, hdisj⟩ := hG s t hinj
  
  let paths' : ∀ i : Fin k, G.Walk (s' i) (t' i) := fun i =>
    (paths ⟨i.val, by omega⟩).copy (hs_emb i) (ht_emb i)
  refine ⟨paths', ?_, ?_⟩
  · 
    intro i
    change ((paths ⟨i.val, by omega⟩).copy (hs_emb i) (ht_emb i)).IsPath
    rw [Walk.isPath_copy]
    exact hIsPath ⟨i.val, by omega⟩
  · 
    intro i j hij
    have hij_lifted :
        (⟨i.val, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val, by omega⟩ := by
      intro heq
      apply hij
      have hij_val : i.val = j.val := Fin.mk.inj_iff.mp heq
      exact Fin.ext hij_val
    have h1 := hdisj hij_lifted
    
    
    have hsupp_i : (paths' i).internalSupport =
        (paths ⟨i.val, by omega⟩).internalSupport := by
      change ((paths ⟨i.val, by omega⟩).copy (hs_emb i) (ht_emb i)).internalSupport =
        (paths ⟨i.val, by omega⟩).internalSupport
      ext x
      simp only [Walk.mem_internalSupport, Walk.support_copy]
      constructor
      · rintro ⟨hxs, hne1, hne2⟩
        refine ⟨hxs, ?_, ?_⟩
        · intro hx
          apply hne1
          rw [hx, hs_emb]
        · intro hx
          apply hne2
          rw [hx, ht_emb]
      · rintro ⟨hxs, hne1, hne2⟩
        refine ⟨hxs, ?_, ?_⟩
        · intro hx
          apply hne1
          rw [hx, ← hs_emb]
        · intro hx
          apply hne2
          rw [hx, ← ht_emb]
    have hsupp_j : (paths' j).internalSupport =
        (paths ⟨j.val, by omega⟩).internalSupport := by
      change ((paths ⟨j.val, by omega⟩).copy (hs_emb j) (ht_emb j)).internalSupport =
        (paths ⟨j.val, by omega⟩).internalSupport
      ext x
      simp only [Walk.mem_internalSupport, Walk.support_copy]
      constructor
      · rintro ⟨hxs, hne1, hne2⟩
        refine ⟨hxs, ?_, ?_⟩
        · intro hx
          apply hne1
          rw [hx, hs_emb]
        · intro hx
          apply hne2
          rw [hx, ht_emb]
      · rintro ⟨hxs, hne1, hne2⟩
        refine ⟨hxs, ?_, ?_⟩
        · intro hx
          apply hne1
          rw [hx, ← hs_emb]
        · intro hx
          apply hne2
          rw [hx, ← ht_emb]
    rw [hsupp_i, hsupp_j]
    exact h1


theorem IsKLinked.le {G : SimpleGraph V} {k k' : ℕ}
    (hcard : 2 * k ≤ Fintype.card V)
    (hkle : k' ≤ k) (h : G.IsKLinked k) : G.IsKLinked k' := by
  classical
  
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hkle
  
  
  clear hkle
  subst hn
  induction n with
  | zero => exact h
  | succ n ih =>
      apply ih
      · 
        omega
      · 
        have hcard' : 2 * ((k' + n) + 1) ≤ Fintype.card V := by
          have : k' + (n + 1) = (k' + n) + 1 := by ring
          rw [this] at hcard
          exact hcard
        
        have hrw : (k' + n) + 1 = k' + (n + 1) := by ring
        have h_succ : G.IsKLinked ((k' + n) + 1) := by
          rw [hrw]; exact h
        exact h_succ.pred hcard'

end IsKLinkedMonotone



section MinSeparatorEqVertexConnectivity

variable [Fintype V] [DecidableEq V]


theorem IsKConnected.exists_minSeparator_card_eq_vertexConnectivity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : G.vertexConnectivity + 1 < Fintype.card V) :
    ∃ S : Finset V, G.IsMinSeparator S ∧ S.card = G.vertexConnectivity := by
  classical
  set κ : ℕ := G.vertexConnectivity with hκdef
  
  have hcard' : κ + 1 + 1 ≤ Fintype.card V := by omega
  have hcardκ : κ + 1 ≤ Fintype.card V := by omega
  
  have hnot : ¬ G.IsKConnected (κ + 1) := by
    intro h
    
    unfold IsKConnected at h
    omega
  
  obtain ⟨S, hScard, hSmin⟩ :=
    (IsKConnected.not_iff_exists_minSeparator_lt G hcard').mp hnot
  
  
  have hKκ : G.IsKConnected κ := by
    unfold IsKConnected; exact le_refl _
  have hge := (IsKConnected.iff_all_minSeparator_card_ge G hcardκ).mp hKκ S hSmin
  
  refine ⟨S, hSmin, ?_⟩
  omega

end MinSeparatorEqVertexConnectivity



section IsKLinkedImpKConnectedOne

variable [Fintype V] [DecidableEq V]


theorem IsKLinked.imp_isKConnected_one
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (hcard : 2 * k ≤ Fintype.card V)
    (hG : G.IsKLinked k) : G.IsKConnected 1 := by
  classical
  
  have hG1 : G.IsKLinked 1 := IsKLinked.le hcard hk hG
  
  have hreach : ∀ u v : V, u ≠ v → G.Reachable u v :=
    isKLinked_one_iff.mp hG1
  
  haveI hnt : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    omega
  
  have hConn : G.Connected := by
    refine ⟨?_⟩
    intro u v
    by_cases huv : u = v
    · subst huv; exact Reachable.refl u
    · exact hreach u v huv
  
  have hConnInduce : (G.induce (Set.univ : Set V)).Connected :=
    (connected_induce_univ_iff G).mpr hConn
  
  have hVC : G.IsVertexConnected 1 := by
    refine ⟨?_, ?_⟩
    · 
      rw [← Fintype.one_lt_card_iff_nontrivial] at hnt
      exact hnt
    · 
      intro S hS
      
      have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hSempty
      
      
      have hcoe : ((↑(Finset.univ \ (∅ : Finset V)) : Set V)) = Set.univ := by
        simp
      rw [hcoe]
      exact hConnInduce
  
  unfold IsKConnected
  exact le_vertexConnectivity_of_isVertexConnected G hVC

end IsKLinkedImpKConnectedOne



section EdgeSeparator


def IsEdgeSeparator (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  ¬ (G.deleteEdges F).Connected


lemma isEdgeSeparator_iff_not_connected_after_delete
    {G : SimpleGraph V} {F : Set (Sym2 V)} :
    G.IsEdgeSeparator F ↔ ¬ (G.deleteEdges F).Connected := Iff.rfl


lemma IsEdgeSeparator.mono {G : SimpleGraph V} {F F' : Set (Sym2 V)}
    (hsub : F ⊆ F') (h : G.IsEdgeSeparator F) : G.IsEdgeSeparator F' := by
  unfold IsEdgeSeparator at *
  intro hConn
  apply h
  have hle : G.deleteEdges F' ≤ G.deleteEdges F := deleteEdges_anti hsub
  exact hConn.mono hle

end EdgeSeparator



section Bridge


def IsBridge' (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ G.IsEdgeSeparator {e}


lemma IsBridge'.mem_edgeSet {G : SimpleGraph V} {e : Sym2 V}
    (he : G.IsBridge' e) : e ∈ G.edgeSet := he.1


lemma isBridge'_iff {G : SimpleGraph V} {e : Sym2 V} :
    G.IsBridge' e ↔ e ∈ G.edgeSet ∧ G.IsEdgeSeparator {e} := Iff.rfl

end Bridge



section BridgeEndpoints


theorem IsBridge.endpoints_not_reachable_after_delete
    {G : SimpleGraph V} {u v : V} (he : G.IsBridge (s(u, v) : Sym2 V)) :
    ¬ (G.deleteEdges {s(u, v)}).Reachable u v := by
  rw [isBridge_iff] at he
  exact he.2


theorem IsBridge.toIsBridge'
    {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (he : G.IsBridge (s(u, v) : Sym2 V)) :
    G.IsBridge' (s(u, v) : Sym2 V) := by
  refine ⟨huv, ?_⟩
  intro hConn
  exact he.endpoints_not_reachable_after_delete (hConn.preconnected u v)

end BridgeEndpoints



section MinEdgeSeparator


structure IsMinEdgeSeparator (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop where
  
  isEdgeSeparator : G.IsEdgeSeparator (F : Set (Sym2 V))
  
  minimal : ∀ F' : Finset (Sym2 V), F' ⊂ F → ¬ G.IsEdgeSeparator (F' : Set (Sym2 V))


theorem IsMinEdgeSeparator.toIsEdgeSeparator
    {G : SimpleGraph V} {F : Finset (Sym2 V)}
    (hmin : G.IsMinEdgeSeparator F) : G.IsEdgeSeparator (F : Set (Sym2 V)) :=
  hmin.isEdgeSeparator


theorem exists_minEdgeSeparator_subset_of_edgeSeparator
    {G : SimpleGraph V} {F : Finset (Sym2 V)}
    (hF : G.IsEdgeSeparator (F : Set (Sym2 V))) :
    ∃ F' : Finset (Sym2 V), F' ⊆ F ∧ G.IsMinEdgeSeparator F' := by
  classical
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    by_cases hmin : ∀ F' : Finset (Sym2 V), F' ⊂ F →
        ¬ G.IsEdgeSeparator (F' : Set (Sym2 V))
    · exact ⟨F, subset_refl F, ⟨hF, hmin⟩⟩
    · push Not at hmin
      obtain ⟨F', hF'sub, hF'sep⟩ := hmin
      have hF'card : F'.card < F.card := Finset.card_lt_card hF'sub
      rw [hn] at hF'card
      obtain ⟨F'', hF''sub, hF''min⟩ := ih F'.card hF'card hF'sep rfl
      exact ⟨F'', hF''sub.trans hF'sub.subset, hF''min⟩

end MinEdgeSeparator



section EdgeSeparatorEndpoints


lemma reachable_deleteEdges_of_walk_deleteEdges_erase
    {G : SimpleGraph V} [DecidableEq V]
    {F : Finset (Sym2 V)} {u v : V}
    (hreach : (G.deleteEdges (F : Set (Sym2 V))).Reachable u v)
    {a b : V}
    (w : (G.deleteEdges ((F.erase s(u, v) : Finset (Sym2 V)) : Set (Sym2 V))).Walk a b) :
    (G.deleteEdges (F : Set (Sym2 V))).Reachable a b := by
  classical
  
  induction w with
  | nil => exact Reachable.refl _
  | @cons a x b hadj p ih =>
      
      
      rw [SimpleGraph.deleteEdges_adj] at hadj
      obtain ⟨hG_ax, hax_notin⟩ := hadj
      
      by_cases hax_F : s(a, x) ∈ (F : Set (Sym2 V))
      · 
        have hax_F_finset : s(a, x) ∈ F := hax_F
        have hax_notin_finset : s(a, x) ∉ F.erase s(u, v) := by
          intro h
          apply hax_notin
          show s(a, x) ∈ ((F.erase s(u, v) : Finset (Sym2 V)) : Set (Sym2 V))
          exact_mod_cast h
        
        
        have hax_eq_e : s(a, x) = s(u, v) := by
          by_contra hne
          exact hax_notin_finset (Finset.mem_erase.mpr ⟨hne, hax_F_finset⟩)
        
        rw [Sym2.eq_iff] at hax_eq_e
        have hReach_ax : (G.deleteEdges (F : Set (Sym2 V))).Reachable a x := by
          rcases hax_eq_e with ⟨ha_u, hx_v⟩ | ⟨ha_v, hx_u⟩
          · subst ha_u; subst hx_v; exact hreach
          · subst ha_v; subst hx_u; exact hreach.symm
        
        exact hReach_ax.trans ih
      · 
        have hadj_GF : (G.deleteEdges (F : Set (Sym2 V))).Adj a x := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hG_ax, hax_F⟩
        exact hadj_GF.reachable.trans ih


lemma reachable_deleteEdges_of_reachable_deleteEdges_erase
    {G : SimpleGraph V} [DecidableEq V]
    {F : Finset (Sym2 V)} {u v : V}
    (hreach : (G.deleteEdges (F : Set (Sym2 V))).Reachable u v)
    {a b : V}
    (hab : (G.deleteEdges ((F.erase s(u, v) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b) :
    (G.deleteEdges (F : Set (Sym2 V))).Reachable a b := by
  classical
  obtain ⟨w⟩ := hab
  exact reachable_deleteEdges_of_walk_deleteEdges_erase hreach w


theorem IsMinEdgeSeparator.endpoints_not_reachable_after_delete
    {G : SimpleGraph V} [DecidableEq V]
    {F : Finset (Sym2 V)} (hmin : G.IsMinEdgeSeparator F)
    {u v : V} (he : s(u, v) ∈ F) :
    ¬ (G.deleteEdges (F : Set (Sym2 V))).Reachable u v := by
  classical
  intro hreach
  
  have hsub : (F.erase s(u, v)) ⊂ F := Finset.erase_ssubset he
  
  have hnot : ¬ G.IsEdgeSeparator ((F.erase s(u, v) : Finset (Sym2 V)) : Set (Sym2 V)) :=
    hmin.minimal _ hsub
  apply hnot
  
  
  unfold IsEdgeSeparator
  intro hConn
  
  
  
  apply hmin.isEdgeSeparator
  have hNonempty : Nonempty V := hConn.nonempty
  refine ⟨?_⟩
  intro a b
  exact reachable_deleteEdges_of_reachable_deleteEdges_erase hreach
    (hConn.preconnected a b)


theorem IsMinEdgeSeparator.exists_endpoints_not_reachable
    {G : SimpleGraph V} [DecidableEq V]
    {F : Finset (Sym2 V)} (hmin : G.IsMinEdgeSeparator F)
    {e : Sym2 V} (he : e ∈ F) :
    ∃ u v : V, e = s(u, v) ∧
      ¬ (G.deleteEdges (F : Set (Sym2 V))).Reachable u v := by
  classical
  
  induction e with
  | h u v =>
      refine ⟨u, v, rfl, ?_⟩
      exact hmin.endpoints_not_reachable_after_delete he

end EdgeSeparatorEndpoints



section BridgeEquivalence


theorem isBridge_iff_isBridge'_of_connected
    {G : SimpleGraph V} (hConn : G.Connected) {u v : V} (huv : G.Adj u v) :
    G.IsBridge (s(u, v) : Sym2 V) ↔ G.IsBridge' (s(u, v) : Sym2 V) := by
  refine ⟨fun h => h.toIsBridge' huv, fun hbridge' => ?_⟩
  
  
  have hnotConn : ¬ (G.deleteEdges {s(u, v)}).Connected := hbridge'.2
  
  by_contra hnot
  exact hnotConn (hConn.connected_delete_edge_of_not_isBridge hnot)

end BridgeEquivalence



section BridgeNotInCycle


theorem IsBridge'.not_in_cycle
    {G : SimpleGraph V} (hConn : G.Connected)
    {e : Sym2 V} (he : G.IsBridge' e)
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    e ∉ c.edges := by
  
  induction e with
  | h a b =>
    
    have hab : G.Adj a b := (G.mem_edgeSet).mp he.mem_edgeSet
    
    have hMathlib : G.IsBridge (s(a, b) : Sym2 V) :=
      (isBridge_iff_isBridge'_of_connected hConn hab).mpr he
    
    exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hMathlib).2 c hc


theorem IsBridge'.iff_not_in_cycle
    {G : SimpleGraph V} (hConn : G.Connected)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge' e ↔ ∀ ⦃u : V⦄ (c : G.Walk u u), c.IsCycle → e ∉ c.edges := by
  refine ⟨fun hbridge _ c hc => hbridge.not_in_cycle hConn hc, ?_⟩
  
  intro hno
  
  induction e with
  | h a b =>
    have hab : G.Adj a b := (G.mem_edgeSet).mp he
    
    have hMathlib : G.IsBridge (s(a, b) : Sym2 V) :=
      SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem.mpr ⟨hab, hno⟩
    exact (isBridge_iff_isBridge'_of_connected hConn hab).mp hMathlib

end BridgeNotInCycle



section MinEdgeSeparatorConnectivity

variable [Fintype V] [DecidableEq V]


def IsKEdgeConnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : Nat) : Prop :=
  k <= G.edgeConnectivity


lemma isKEdgeConnected_iff_le_edgeConnectivity {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : Nat} :
    G.IsKEdgeConnected k ↔ k <= G.edgeConnectivity := Iff.rfl


theorem IsKEdgeConnected.isEdgeConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (h : G.IsKEdgeConnected k) :
    G.IsEdgeConnected k := by
  have hec := edgeConnectivity_spec G
  unfold IsKEdgeConnected at h
  intro u v
  exact (hec u v).anti h


theorem not_isKEdgeConnected_extract
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    {k : ℕ} (h : ¬ G.IsKEdgeConnected k) :
    ∃ F : Finset (Sym2 V), F.card < k ∧ G.IsEdgeSeparator (F : Set (Sym2 V)) := by
  classical
  
  have hk_pos : 0 < k := by
    by_contra hk0
    push Not at hk0
    interval_cases k
    
    exact h (Nat.zero_le _)
  
  by_contra hAll
  
  push Not at hAll
  
  
  
  
  have hEC : G.IsEdgeConnected k := by
    intro u v s hs
    
    
    
    have hsfin : s.Finite := by
      have : s.encard < (k : ℕ∞) := hs
      by_contra hinf
      rw [Set.not_finite] at hinf
      rw [hinf.encard_eq] at this
      exact absurd this (by simp)
    
    set F : Finset (Sym2 V) := hsfin.toFinset with hFdef
    have hFcoe : (F : Set (Sym2 V)) = s := by
      rw [hFdef]; exact hsfin.coe_toFinset
    have hFcard : F.card < k := by
      have : (s.encard : ℕ∞) = (F.card : ℕ∞) := by
        rw [← hFcoe, Set.encard_coe_eq_coe_finsetCard]
      have hk_enat : (F.card : ℕ∞) < (k : ℕ∞) := by rw [← this]; exact hs
      exact_mod_cast hk_enat
    
    have hNotSep : ¬ G.IsEdgeSeparator (F : Set (Sym2 V)) := hAll F hFcard
    
    unfold IsEdgeSeparator at hNotSep
    push Not at hNotSep
    
    have hConn : (G.deleteEdges s).Connected := by
      rw [← hFcoe]; exact hNotSep
    exact hConn.preconnected u v
  
  have hkle : k ≤ G.edgeConnectivity :=
    le_edgeConnectivity_of_isEdgeConnected G hEC
  exact h hkle


theorem IsKEdgeConnected.not_iff_exists_minEdgeSeparator_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    {k : ℕ} :
    ¬ G.IsKEdgeConnected k ↔
      ∃ F : Finset (Sym2 V), F.card < k ∧ G.IsMinEdgeSeparator F := by
  classical
  constructor
  · 
    intro hnot
    obtain ⟨F, hFcard, hFsep⟩ := G.not_isKEdgeConnected_extract hnot
    obtain ⟨F', hF'subF, hF'min⟩ :=
      exists_minEdgeSeparator_subset_of_edgeSeparator hFsep
    refine ⟨F', ?_, hF'min⟩
    exact lt_of_le_of_lt (Finset.card_le_card hF'subF) hFcard
  · 
    rintro ⟨F, hFcard, hFmin⟩ hKEC
    
    have hEC : G.IsEdgeConnected k := hKEC.isEdgeConnected
    
    have hencard : ((F : Set (Sym2 V))).encard < (k : ℕ∞) := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hFcard
    
    
    
    
    
    have hPre : (G.deleteEdges (F : Set (Sym2 V))).Preconnected := by
      intro u v
      exact hEC u v hencard
    have hConn : (G.deleteEdges (F : Set (Sym2 V))).Connected :=
      ⟨hPre⟩
    exact hFmin.isEdgeSeparator hConn


theorem IsKEdgeConnected.iff_all_minEdgeSeparator_card_ge
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    {k : ℕ} :
    G.IsKEdgeConnected k ↔
      ∀ F : Finset (Sym2 V), G.IsMinEdgeSeparator F → k ≤ F.card := by
  classical
  constructor
  · 
    intro hKEC F hFmin
    by_contra hFcard
    push Not at hFcard
    
    
    have hnot : ¬ G.IsKEdgeConnected k :=
      (IsKEdgeConnected.not_iff_exists_minEdgeSeparator_lt G).mpr ⟨F, hFcard, hFmin⟩
    exact hnot hKEC
  · 
    intro hAll
    by_contra hnot
    
    obtain ⟨F, hFcard, hFmin⟩ :=
      (IsKEdgeConnected.not_iff_exists_minEdgeSeparator_lt G).mp hnot
    exact absurd (hAll F hFmin) (Nat.not_le_of_lt hFcard)




theorem IsKEdgeConnected.exists_minEdgeSeparator_card_eq_edgeConnectivity
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] :
    ∃ F : Finset (Sym2 V), G.IsMinEdgeSeparator F ∧ F.card = G.edgeConnectivity := by
  classical
  set lam : ℕ := G.edgeConnectivity with hlamdef
  
  have hnot : ¬ G.IsKEdgeConnected (lam + 1) := by
    intro h
    
    unfold IsKEdgeConnected at h
    omega
  
  obtain ⟨F, hFcard, hFmin⟩ :=
    (IsKEdgeConnected.not_iff_exists_minEdgeSeparator_lt G).mp hnot
  
  
  have hKlam : G.IsKEdgeConnected lam := by
    unfold IsKEdgeConnected; exact le_refl _
  have hge := (IsKEdgeConnected.iff_all_minEdgeSeparator_card_ge G).mp hKlam F hFmin
  
  refine ⟨F, hFmin, ?_⟩
  omega




theorem edgeConnectivity_le_card_minEdgeSeparator
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nontrivial V]
    {F : Finset (Sym2 V)} (hF : G.IsMinEdgeSeparator F) :
    G.edgeConnectivity ≤ F.card := by
  classical
  
  have hKlam : G.IsKEdgeConnected G.edgeConnectivity := by
    unfold IsKEdgeConnected; exact le_refl _
  exact (IsKEdgeConnected.iff_all_minEdgeSeparator_card_ge G).mp hKlam F hF




theorem IsBridge'.iff_isMinEdgeSeparator_singleton
    {G : SimpleGraph V} [DecidableRel G.Adj] {e : Sym2 V}
    (hconn : G.Connected) (he : e ∈ G.edgeSet) :
    G.IsBridge' e ↔ G.IsMinEdgeSeparator ({e} : Finset (Sym2 V)) := by
  classical
  constructor
  · 
    intro hbr
    
    have hsep : G.IsEdgeSeparator (({e} : Finset (Sym2 V)) : Set (Sym2 V)) := by
      have : G.IsEdgeSeparator ({e} : Set (Sym2 V)) := hbr.2
      simpa using this
    refine ⟨hsep, ?_⟩
    
    intro F' hF'lt
    
    
    have hF'eq : F' = (∅ : Finset (Sym2 V)) := by
      rcases Finset.ssubset_singleton_iff.mp hF'lt with h
      exact h
    subst hF'eq
    
    intro hsepEmpty
    
    
    unfold IsEdgeSeparator at hsepEmpty
    apply hsepEmpty
    
    have hempty : ((∅ : Finset (Sym2 V)) : Set (Sym2 V)) = (∅ : Set (Sym2 V)) := by
      simp
    rw [hempty, SimpleGraph.deleteEdges_empty]
    exact hconn
  · 
    intro hmin
    refine ⟨he, ?_⟩
    
    have : G.IsEdgeSeparator (({e} : Finset (Sym2 V)) : Set (Sym2 V)) :=
      hmin.toIsEdgeSeparator
    simpa using this

end MinEdgeSeparatorConnectivity



section TreeBridgeCharacterization


theorem IsTree.every_edge_isBridge
    {G : SimpleGraph V} (hG : G.IsTree) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge' e := by
  
  refine (IsBridge'.iff_not_in_cycle hG.connected he).mpr ?_
  
  intro u c hcyc _
  exact hG.isAcyclic c hcyc


theorem connected_and_every_edge_isBridge_imp_isTree
    {G : SimpleGraph V} (hConn : G.Connected)
    (hBridge : ∀ e ∈ G.edgeSet, G.IsBridge' e) :
    G.IsTree := by
  refine ⟨hConn, ?_⟩
  
  intro v c hcyc
  
  have hlen : 0 < c.edges.length := by
    rw [Walk.length_edges]
    exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hcyc.three_le_length
  
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hlen
  
  have hmem : e ∈ G.edgeSet := c.edges_subset_edgeSet he
  
  have hbridge : G.IsBridge' e := hBridge e hmem
  
  exact (IsBridge'.iff_not_in_cycle hConn hmem).mp hbridge c hcyc he


theorem IsTree.iff_connected_and_every_edge_isBridge
    {G : SimpleGraph V} :
    G.IsTree ↔ G.Connected ∧ ∀ e ∈ G.edgeSet, G.IsBridge' e :=
  ⟨fun hT => ⟨hT.connected, fun _ he => hT.every_edge_isBridge he⟩,
   fun ⟨hC, hB⟩ => connected_and_every_edge_isBridge_imp_isTree hC hB⟩

end TreeBridgeCharacterization



section TreeEdgeConnectivity

variable [Fintype V] [DecidableEq V]


theorem IsTree.edgeConnectivity_eq_one
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    G.edgeConnectivity = 1 := by
  classical
  
  have hNt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  
  have hle : G.edgeConnectivity ≤ 1 := by
    
    have hcardE : 1 ≤ G.edgeFinset.card := by
      have hcardEV : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
      omega
    
    have hne : G.edgeFinset.Nonempty := Finset.card_pos.mp hcardE
    obtain ⟨e, he⟩ := hne
    have heSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
    
    have hbr : G.IsBridge' e := hT.every_edge_isBridge heSet
    
    have hmin : G.IsMinEdgeSeparator ({e} : Finset (Sym2 V)) :=
      (IsBridge'.iff_isMinEdgeSeparator_singleton hT.connected heSet).mp hbr
    
    have hge_lam : G.edgeConnectivity ≤ ({e} : Finset (Sym2 V)).card :=
      edgeConnectivity_le_card_minEdgeSeparator hmin
    simpa using hge_lam
  
  have hge : 1 ≤ G.edgeConnectivity := by
    have hPre : G.Preconnected := hT.connected.preconnected
    have hEC : G.IsEdgeConnected 1 := SimpleGraph.isEdgeConnected_one.mpr hPre
    exact le_edgeConnectivity_of_isEdgeConnected G hEC
  exact le_antisymm hle hge

end TreeEdgeConnectivity



section EdgeConnectivityBridge

variable [Fintype V] [DecidableEq V]


theorem edgeConnectivity_le_one_iff_exists_bridge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hConn : G.Connected) (hcard : 2 ≤ Fintype.card V) :
    G.edgeConnectivity ≤ 1 ↔ ∃ e ∈ G.edgeSet, G.IsBridge' e := by
  classical
  
  have hNt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  constructor
  · 
    intro hle
    
    obtain ⟨F, hFmin, hFcard⟩ :=
      IsKEdgeConnected.exists_minEdgeSeparator_card_eq_edgeConnectivity G
    
    have hFle : F.card ≤ 1 := hFcard ▸ hle
    
    interval_cases hFc : F.card
    · 
      exfalso
      have hFempty : F = (∅ : Finset (Sym2 V)) := Finset.card_eq_zero.mp hFc
      subst hFempty
      have hsep : G.IsEdgeSeparator ((∅ : Finset (Sym2 V)) : Set (Sym2 V)) :=
        hFmin.toIsEdgeSeparator
      
      unfold IsEdgeSeparator at hsep
      apply hsep
      have hcoe : ((∅ : Finset (Sym2 V)) : Set (Sym2 V)) = (∅ : Set (Sym2 V)) := by simp
      rw [hcoe, SimpleGraph.deleteEdges_empty]
      exact hConn
    · 
      obtain ⟨e, hFeq⟩ := Finset.card_eq_one.mp hFc
      subst hFeq
      
      
      have heSet : e ∈ G.edgeSet := by
        by_contra hne
        have hsep : G.IsEdgeSeparator (({e} : Finset (Sym2 V)) : Set (Sym2 V)) :=
          hFmin.toIsEdgeSeparator
        unfold IsEdgeSeparator at hsep
        apply hsep
        have hcoe : (({e} : Finset (Sym2 V)) : Set (Sym2 V)) = ({e} : Set (Sym2 V)) := by simp
        rw [hcoe]
        
        have heq : G.deleteEdges {e} = G := by
          ext a b
          simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
          refine ⟨fun ⟨hab, _⟩ => hab, fun hab => ⟨hab, ?_⟩⟩
          intro hee
          
          have : s(a, b) ∈ G.edgeSet := hab
          exact hne (hee ▸ this)
        rw [heq]
        exact hConn
      
      have hbr : G.IsBridge' e :=
        (IsBridge'.iff_isMinEdgeSeparator_singleton hConn heSet).mpr hFmin
      exact ⟨e, heSet, hbr⟩
  · 
    rintro ⟨e, heSet, hbr⟩
    
    have hmin : G.IsMinEdgeSeparator ({e} : Finset (Sym2 V)) :=
      (IsBridge'.iff_isMinEdgeSeparator_singleton hConn heSet).mp hbr
    
    have h := edgeConnectivity_le_card_minEdgeSeparator hmin
    simpa using h

end EdgeConnectivityBridge



section TreeIffEdgeConnectivityOneBridge

variable [Fintype V] [DecidableEq V]


theorem isTree_iff_edgeConnectivity_eq_one_and_every_edge_isBridge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : 2 ≤ Fintype.card V) :
    G.IsTree ↔ G.edgeConnectivity = 1 ∧ ∀ e ∈ G.edgeSet, G.IsBridge' e := by
  classical
  have hNt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  constructor
  · 
    intro hT
    refine ⟨hT.edgeConnectivity_eq_one hcard, ?_⟩
    intro e he
    exact hT.every_edge_isBridge he
  · 
    rintro ⟨hlam, hBridge⟩
    
    have hKEC : G.IsKEdgeConnected 1 := by
      unfold IsKEdgeConnected; rw [hlam]
    have hEC : G.IsEdgeConnected 1 := hKEC.isEdgeConnected
    have hPre : G.Preconnected := SimpleGraph.isEdgeConnected_one.mp hEC
    have hConn : G.Connected := ⟨hPre⟩
    
    exact connected_and_every_edge_isBridge_imp_isTree hConn hBridge

end TreeIffEdgeConnectivityOneBridge



section HasKDisjointPaths


def HasKDisjointPaths (G : SimpleGraph V) (u v : V) (k : ℕ) : Prop :=
  ∃ paths : Fin k → G.Walk u v,
    (∀ i, (paths i).IsPath) ∧
    Pairwise (fun i j => Disjoint (paths i).internalSupport
                                  (paths j).internalSupport)


theorem HasKDisjointPaths.zero (G : SimpleGraph V) (u v : V) :
    G.HasKDisjointPaths u v 0 := by
  refine ⟨fun i => i.elim0, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i j _; exact i.elim0


theorem HasKDisjointPaths.symm {G : SimpleGraph V} {u v : V} {k : ℕ}
    (h : G.HasKDisjointPaths u v k) : G.HasKDisjointPaths v u k := by
  classical
  obtain ⟨paths, hp_path, hp_disj⟩ := h
  refine ⟨fun i => (paths i).reverse, ?_, ?_⟩
  · intro i; exact (hp_path i).reverse
  · intro i j hij
    
    have hrev : ∀ i, ((paths i).reverse).internalSupport =
        (paths i).internalSupport := by
      intro i
      ext x
      simp only [Walk.mem_internalSupport, Walk.support_reverse,
        List.mem_reverse]
      tauto
    rw [hrev i, hrev j]
    exact hp_disj hij

end HasKDisjointPaths



section MengerEasy

variable [Fintype V] [DecidableEq V]


theorem IsKConnected.of_forall_pairs_disjoint_paths
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hcard : k + 1 ≤ Fintype.card V)
    (h : ∀ u v : V, u ≠ v → G.HasKDisjointPaths u v k) :
    G.IsKConnected k := by
  classical
  by_contra hnot
  
  obtain ⟨S, hScard, hSsep⟩ := G.not_isKConnected_extract hcard hnot
  
  have hSlt : S.card < Fintype.card V := lt_of_lt_of_le hScard (by omega)
  have hcompl_nonempty : ((↑S : Set V))ᶜ.Nonempty := by
    
    have hexists : ∃ x : V, x ∉ S := by
      by_contra hAll
      push Not at hAll
      have : Finset.univ ⊆ S := fun x _ => hAll x
      have : Fintype.card V ≤ S.card := by
        have := Finset.card_le_card this
        simpa using this
      omega
    obtain ⟨x, hx⟩ := hexists
    exact ⟨x, by simp [hx]⟩
  
  obtain ⟨C₁, C₂, hC_ne⟩ := hSsep.exists_two_distinct_components hcompl_nonempty
  
  obtain ⟨⟨c₁, hc₁_notS⟩, hc₁_eq⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₁ := C₁.exists_rep
  obtain ⟨⟨c₂, hc₂_notS⟩, hc₂_eq⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₂ := C₂.exists_rep
  
  have hc_ne : c₁ ≠ c₂ := by
    intro heq
    apply hC_ne
    rw [← hc₁_eq, ← hc₂_eq]
    
    have : (⟨c₁, hc₁_notS⟩ : (((S : Set V))ᶜ : Set V)) = ⟨c₂, hc₂_notS⟩ :=
      Subtype.ext heq
    rw [this]
  
  have hnr : ¬ (G.induce ((S : Set V)ᶜ)).Reachable
        ⟨c₁, hc₁_notS⟩ ⟨c₂, hc₂_notS⟩ := by
    intro hreach
    apply hC_ne
    rw [← hc₁_eq, ← hc₂_eq]
    exact (SimpleGraph.ConnectedComponent.eq).mpr hreach
  
  obtain ⟨paths, hp_path, hp_disj⟩ := h c₁ c₂ hc_ne
  
  have hmeets : ∀ i, ∃ x ∈ (paths i).internalSupport, x ∈ S := by
    intro i
    have hres := Walk.exists_internal_mem_of_not_reachable_compl
      hc₁_notS hc₂_notS hnr (paths i)
    obtain ⟨x, hxi, hxS⟩ := hres
    
    refine ⟨x, hxi, ?_⟩
    simpa using hxS
  
  
  
  let s' : Fin k → V := fun _ => c₁
  let t' : Fin k → V := fun _ => c₂
  let paths' : ∀ i : Fin k, G.Walk (s' i) (t' i) := fun i => paths i
  have hdisj' : InternallyDisjoint paths' := hp_disj
  have hmeets' : ∀ i, ∃ x ∈ (paths' i).internalSupport, x ∈ S := hmeets
  have hk_le : k ≤ S.card :=
    card_ge_of_internally_disjoint_meets paths' S hmeets' hdisj'
  
  exact absurd hk_le (Nat.not_le_of_lt hScard)

end MengerEasy



section MengerBridge


theorem HasKDisjointPaths.iff_nonempty_STDisjointPaths
    {G : SimpleGraph V} {u v : V} {k : ℕ} :
    G.HasKDisjointPaths u v k ↔ Nonempty (G.STDisjointPaths u v k) := by
  constructor
  · 
    rintro ⟨paths, hp_path, hp_disj⟩
    refine ⟨{ walk := paths, isPath := hp_path, internal_disjoint := ?_ }⟩
    
    
    intro i j hij w hwi hwu hwv hwj
    
    have hwi_int : w ∈ (paths i).internalSupport :=
      ⟨hwi, hwu, hwv⟩
    have hwj_int : w ∈ (paths j).internalSupport :=
      ⟨hwj, hwu, hwv⟩
    
    have hdisj : Disjoint (paths i).internalSupport (paths j).internalSupport :=
      hp_disj hij
    rw [Set.disjoint_left] at hdisj
    exact hdisj hwi_int hwj_int
  · 
    rintro ⟨dp⟩
    refine ⟨dp.walk, dp.isPath, ?_⟩
    intro i j hij
    
    rw [Set.disjoint_left]
    intro w hwi hwj
    
    obtain ⟨hwi_supp, hwu, hwv⟩ := hwi
    obtain ⟨hwj_supp, _, _⟩ := hwj
    
    exact dp.internal_disjoint i j hij w hwi_supp hwu hwv hwj_supp

end MengerBridge



section MengerCharacterization

variable [Fintype V] [DecidableEq V]


theorem IsKConnected.iff_forall_pairs_disjoint_paths
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hcard : k + 1 ≤ Fintype.card V) :
    G.IsKConnected k ↔ ∀ u v : V, u ≠ v → G.HasKDisjointPaths u v k := by
  classical
  constructor
  · 
    intro hKConn u v huv
    
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · exact HasKDisjointPaths.zero G u v
    
    haveI hNT : Nontrivial V := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      omega
    
    have hk_lt : k < Fintype.card V := by omega
    
    have hVC : G.IsVertexConnected k := hKConn.isVertexConnected
    
    
    have hsep : ∀ S : Finset V, S.card < k →
        (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected :=
      hVC.2
    
    
    have hSTDP : ∀ a b : V, a ≠ b → Nonempty (G.STDisjointPaths a b k) :=
      (G.stDisjointPaths_iff_connected k hk_lt).mpr hsep
    
    exact HasKDisjointPaths.iff_nonempty_STDisjointPaths.mpr (hSTDP u v huv)
  · 
    intro h
    exact IsKConnected.of_forall_pairs_disjoint_paths hcard h

end MengerCharacterization

/-! ## Fan lemma for k-connected graphs

The fan form of Menger in `SimpleGraph.Connectivity.Menger` is stated as an
exact min--max theorem.  The declarations below extract the standard fan
lemma: in a k-connected graph, a vertex has a k-fan to every set of at least
k other vertices.
-/

section FanLemma

variable [Fintype V] [DecidableEq V]

/-- Restrict an `a`-`B` fan of order `k'` to its first `k <= k'` arms. -/
noncomputable def ABFan.truncate
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a : V} {B : Finset V} {k' : Nat} (P : G.ABFan a B k')
    (k : Nat) (hle : k <= k') : G.ABFan a B k where
  dst := fun i => P.dst (Fin.castLE hle i)
  walk := fun i => P.walk (Fin.castLE hle i)
  isPath := fun i => P.isPath (Fin.castLE hle i)
  dst_mem := fun i => P.dst_mem (Fin.castLE hle i)
  dst_inj := P.dst_inj.comp (Fin.castLE_injective hle)
  touchB := fun i => P.touchB (Fin.castLE hle i)
  common_eq_start := fun i j hij v hvi hvj =>
    P.common_eq_start (Fin.castLE hle i) (Fin.castLE hle j)
      (fun heq => hij (Fin.castLE_injective hle heq)) v hvi hvj

/-- A lower bound for every `a`-`B` separator avoiding `a` produces an
`a`-`B` fan of that order.  This is the inequality-shaped consequence of the
exact fan form of Menger. -/
theorem exists_abFan_of_separator_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (k : Nat) (haB : a ∉ B)
    (hbound : ∀ S : Finset V, a ∉ S ->
      G.IsABSeparator {a} B S -> k <= S.card) :
    Nonempty (G.ABFan a B k) := by
  obtain ⟨P⟩ := abFan_hard_direction G a B haB
  obtain ⟨S, haS, hsep, hcard⟩ := minABFanSeparatorSize_spec G a B haB
  have hle : k <= G.minABFanSeparatorSize a B := by
    simpa [hcard] using hbound S haS hsep
  exact ⟨P.truncate k hle⟩

/-- **Fan lemma** (Diestel, consequence of the fan form of Menger): if `G` is
`k`-connected, `a ∉ B`, and `B` has at least `k` vertices, then `G` contains
an `a`-`B` fan of order `k`. -/
theorem IsKConnected.exists_abFan
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nontrivial V]
    {k : Nat} (hG : G.IsKConnected k)
    (a : V) (B : Finset V) (haB : a ∉ B) (hkB : k <= B.card) :
    Nonempty (G.ABFan a B k) := by
  apply exists_abFan_of_separator_lower_bound G a B k haB
  intro S haS hsep
  by_contra hnot
  push Not at hnot
  have hSB : S.card < B.card := lt_of_lt_of_le hnot hkB
  obtain ⟨b, hbB, hbS⟩ := Finset.exists_mem_notMem_of_card_lt_card hSB
  have hconn := hG.isVertexConnected.2 S hnot
  rw [connected_iff] at hconn
  have ha_mem : a ∈ (↑(Finset.univ \ S) : Set V) := by
    simp [haS]
  have hb_mem : b ∈ (↑(Finset.univ \ S) : Set V) := by
    simp [hbS]
  obtain ⟨w⟩ := hconn.1 ⟨a, ha_mem⟩ ⟨b, hb_mem⟩
  have hw'_avoid : ∀ v ∈
      (Walk.map (Embedding.induce (↑(Finset.univ \ S) : Set V) (G := G)).toHom w).support,
      v ∉ S := by
    intro v hv
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨⟨x, hx⟩, _, rfl⟩ := hv
    exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
  obtain ⟨v, hvw, hvS⟩ := hsep a (by simp) b hbB haS hbS
    (Walk.map (Embedding.induce (↑(Finset.univ \ S) : Set V) (G := G)).toHom w)
  exact hw'_avoid v hvw hvS

end FanLemma

/-! ## Local edge Menger: packing-side foundation

The following representation and easy inequality are the packing side of
Diestel's local edge form of Menger.  The reverse inequality requires a path
transfer through the line graph and is developed separately.
-/

section LocalEdgeMenger

/-- A family of `k` pairwise edge-disjoint `s`-`t` paths. -/
structure STEdgeDisjointPaths (G : SimpleGraph V) (s t : V) (k : Nat) where
  /-- The `k` walks from `s` to `t`. -/
  walk : Fin k → G.Walk s t
  /-- Every walk is a path. -/
  isPath : ∀ i, (walk i).IsPath
  /-- Distinct paths have disjoint edge lists. -/
  edge_disjoint : ∀ i j, i ≠ j → (walk i).edges.Disjoint (walk j).edges

/-- Every graph has an empty family of edge-disjoint `s`-`t` paths. -/
theorem stEdgeDisjointPaths_zero (G : SimpleGraph V) (s t : V) :
    Nonempty (G.STEdgeDisjointPaths s t 0) :=
  ⟨{ walk := Fin.elim0
     isPath := fun i => Fin.elim0 i
     edge_disjoint := fun i => Fin.elim0 i }⟩

/-- Restrict a family of `k'` edge-disjoint paths to its first `k ≤ k'`
members. -/
noncomputable def STEdgeDisjointPaths.truncate
    {G : SimpleGraph V} {s t : V} {k' : Nat}
    (P : G.STEdgeDisjointPaths s t k') (k : Nat) (hle : k ≤ k') :
    G.STEdgeDisjointPaths s t k where
  walk := fun i => P.walk (Fin.castLE hle i)
  isPath := fun i => P.isPath (Fin.castLE hle i)
  edge_disjoint := fun i j hij =>
    P.edge_disjoint (Fin.castLE hle i) (Fin.castLE hle j)
      (fun heq => hij (Fin.castLE_injective hle heq))

/-- **Easy direction of local edge Menger.** If `P` is a family of `k`
pairwise edge-disjoint `s`-`t` paths, every finite edge set whose deletion
separates `s` from `t` has cardinality at least `k`. -/
theorem STEdgeDisjointPaths.card_le_edgeSeparator
    {G : SimpleGraph V} {s t : V} {k : Nat}
    (P : G.STEdgeDisjointPaths s t k) (F : Finset (Sym2 V))
    (hsep : ¬ (G.deleteEdges (F : Set (Sym2 V))).Reachable s t) :
    k ≤ F.card := by
  classical
  have hhit : ∀ i : Fin k, ∃ e : Sym2 V, e ∈ F ∧ e ∈ (P.walk i).edges := by
    intro i
    obtain ⟨e, heF, heP⟩ :=
      (P.walk i).exists_mem_edges_of_not_reachable_deleteEdges hsep
    exact ⟨e, heF, heP⟩
  let f : Fin k → ↥F := fun i =>
    ⟨(hhit i).choose, (hhit i).choose_spec.1⟩
  have hf_edges : ∀ i, (f i : Sym2 V) ∈ (P.walk i).edges :=
    fun i => (hhit i).choose_spec.2
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hval : (f i : Sym2 V) = (f j : Sym2 V) :=
      congrArg Subtype.val hij
    exact P.edge_disjoint i j hne (hf_edges i) (hval ▸ hf_edges j)
  simpa using Fintype.card_le_of_injective f hf_inj

/-! ## Global edge Menger: the packing-to-connectivity direction -/

/-- A family of `k` edge-disjoint `s`-`t` paths makes `s` and `t`
`k`-edge-reachable: deleting fewer than `k` edges cannot meet every path. -/
theorem STEdgeDisjointPaths.isEdgeReachable
    {G : SimpleGraph V} {s t : V} {k : Nat}
    (P : G.STEdgeDisjointPaths s t k) : G.IsEdgeReachable k s t := by
  classical
  intro F hF
  have hFfinite : F.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    rw [hinf.encard_eq] at hF
    exact (not_lt_of_ge (OrderTop.le_top (k : ℕ∞))) hF
  let FF : Finset (Sym2 V) := hFfinite.toFinset
  have hFFcoe : (FF : Set (Sym2 V)) = F := by
    simpa only [FF] using hFfinite.coe_toFinset
  have hFFcard : FF.card < k := by
    have hFFcard' : (FF.card : ℕ∞) < (k : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, hFFcoe]
      exact hF
    exact_mod_cast hFFcard'
  by_contra hnotReach
  have hle : k ≤ FF.card :=
    P.card_le_edgeSeparator FF (by simpa only [hFFcoe] using hnotReach)
  exact (Nat.not_le_of_lt hFFcard) hle

/-- **Easy direction of global edge Menger (Diestel Theorem 3.3.5(ii)).**
If every pair of distinct vertices has `k` pairwise edge-disjoint paths, then
the graph is `k`-edge-connected. The reverse implication is the hard local
edge-Menger direction and is developed separately. -/
theorem IsKEdgeConnected.of_forall_pairs_edgeDisjointPaths
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [Nontrivial V] {k : Nat}
    (h : ∀ s t : V, s ≠ t → Nonempty (G.STEdgeDisjointPaths s t k)) :
    G.IsKEdgeConnected k := by
  apply le_edgeConnectivity_of_isEdgeConnected G
  intro s t
  by_cases hst : s = t
  · subst t
    exact IsEdgeReachable.refl s
  · exact (h s t hst).some.isEdgeReachable

end LocalEdgeMenger

/-! ## Book-faithful k-linked graphs are k-connected -/

section IsKLinkedStrongImpKConnected

/-- The book-faithful notion of a **k-linked graph**: for every ordered family
of `2k` distinct terminals there are `k` paths joining the prescribed pairs,
and distinct paths are vertex-disjoint on their entire supports.

This is intentionally stronger than the historical MdsLean predicate
`IsKLinked`, whose `InternallyDisjoint` field only compares internal vertices
and therefore allows a terminal of one path to lie on another path.  Full
support disjointness is the convention used in Diestel §3.6 and is essential
for the standard implication from k-linkedness to k-connectivity. -/
def IsKLinkedStrong (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (s t : Fin k → V), Function.Injective (Sum.elim s t) →
    ∃ paths : ∀ i : Fin k, G.Walk (s i) (t i),
      (∀ i, (paths i).IsPath) ∧
      ∀ i j, i ≠ j →
        Disjoint ({v | v ∈ (paths i).support} : Set V)
          ({v | v ∈ (paths j).support} : Set V)

/-- Book-faithful k-linkedness implies the historical MdsLean predicate.
Only this direction is valid: internal-support disjointness does not prevent a
terminal of one path from occurring on another path. -/
theorem IsKLinkedStrong.toIsKLinked
    {G : SimpleGraph V} {k : Nat} (hG : G.IsKLinkedStrong k) :
    G.IsKLinked k := by
  intro s t hinj
  obtain ⟨paths, hpath, hfull⟩ := hG s t hinj
  refine ⟨paths, hpath, ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact Set.disjoint_left.mp (hfull i j hij) hvi.1 hvj.1

variable [Fintype V] [DecidableEq V]

/-- **Every k-linked graph is k-connected** (Diestel §3.6).

Here `IsKLinkedStrong` is the book-faithful definition: distinct prescribed
paths have disjoint full vertex supports.  Assume `2k ≤ |V|`, as in the book's
definition of k-linkedness.  If a set `S` of fewer than `k` vertices separated
`u` from `v`, extend `S ∪ {u}` to a k-set `A` avoiding `v`, choose a disjoint
k-set `B` containing `v`, and prescribe a linkage in which `u` is paired with
`v`.  Every vertex of `S` is the start of another linkage path, so full support
disjointness forces the `u`-`v` path to avoid `S`, contradicting separation.

The analogous statement is false for the legacy `IsKLinked` predicate, which
only requires internal-support disjointness. -/
theorem IsKLinkedStrong.isKConnected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKLinkedStrong k)
    (hcard : 2 * k ≤ Fintype.card V) :
    G.IsKConnected k := by
  classical
  by_cases hk : k = 0
  · subst k
    exact Nat.zero_le _
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_contra hnot
  have hkcard : k + 1 ≤ Fintype.card V := by omega
  obtain ⟨S, hScard, hSsep⟩ := G.not_isKConnected_extract hkcard hnot
  have hSlt : S.card < Fintype.card V := by omega
  have hcompl_nonempty : ((↑S : Set V))ᶜ.Nonempty := by
    obtain ⟨u, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hSlt
    exact ⟨u, by simpa using hu⟩
  obtain ⟨C₁, C₂, hCne⟩ := hSsep.exists_two_distinct_components hcompl_nonempty
  obtain ⟨⟨u, huS⟩, huC⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₁ := C₁.exists_rep
  obtain ⟨⟨v, hvS⟩, hvC⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₂ := C₂.exists_rep
  have huv : u ≠ v := by
    intro huv
    apply hCne
    rw [← huC, ← hvC]
    exact congrArg _ (Subtype.ext huv)
  have hnr : ¬ (G.induce ((S : Set V)ᶜ)).Reachable ⟨u, huS⟩ ⟨v, hvS⟩ := by
    intro hreach
    apply hCne
    rw [← huC, ← hvC]
    exact (SimpleGraph.ConnectedComponent.eq).mpr hreach

  let baseA : Finset V := S ∪ {u}
  let availA : Finset V := Finset.univ.erase v
  have hbaseA_sub : baseA ⊆ availA := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    constructor
    · rintro rfl
      rcases hx with hxS | hxU
      · exact hvS hxS
      · exact huv hxU.symm
    · exact Finset.mem_univ x
  have hbaseA_card : baseA.card ≤ k := by
    calc
      baseA.card ≤ S.card + ({u} : Finset V).card := by
        simpa only [baseA] using Finset.card_union_le S {u}
      _ ≤ k := by simp; omega
  have hk_availA : k ≤ availA.card := by
    simp only [availA, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    omega
  obtain ⟨A, hbaseA_A, hA_avail, hAcard⟩ :=
    Finset.exists_subsuperset_card_eq hbaseA_sub hbaseA_card hk_availA
  have huA : u ∈ A := hbaseA_A (by simp [baseA])
  have hSA : S ⊆ A := fun x hx => hbaseA_A (by simp [baseA, hx])
  have hvA : v ∉ A := by
    intro hv
    exact (Finset.mem_erase.mp (hA_avail hv)).1 rfl

  let availB : Finset V := Finset.univ \ A
  have hv_availB : v ∈ availB := by simp [availB, hvA]
  have hsingleton_sub : ({v} : Finset V) ⊆ availB := by simpa
  have hsingleton_card : ({v} : Finset V).card ≤ k := by simp; omega
  have hk_availB : k ≤ availB.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp only [Finset.card_univ, hAcard]
    omega
  obtain ⟨B, hvBsub, hB_avail, hBcard⟩ :=
    Finset.exists_subsuperset_card_eq hsingleton_sub hsingleton_card hk_availB
  have hvB : v ∈ B := hvBsub (by simp)
  have hAB : Disjoint A B := Finset.disjoint_left.mpr fun x hxA hxB =>
    (Finset.mem_sdiff.mp (hB_avail hxB)).2 hxA

  have eqA : A ≃ Fin k := hAcard ▸ A.equivFin
  have eqB : B ≃ Fin k := hBcard ▸ B.equivFin
  let iu : Fin k := eqA ⟨u, huA⟩
  let iv : Fin k := eqB ⟨v, hvB⟩
  let swapB : Fin k ≃ Fin k := Equiv.swap iu iv
  let s : Fin k → V := fun i => (eqA.symm i).val
  let t : Fin k → V := fun i => (eqB.symm (swapB i)).val
  have hs_inj : Function.Injective s :=
    Subtype.val_injective.comp eqA.symm.injective
  have ht_inj : Function.Injective t :=
    Subtype.val_injective.comp (eqB.symm.injective.comp swapB.injective)
  have hst_ne : ∀ i j, s i ≠ t j := by
    intro i j heq
    have hsA : s i ∈ A := (eqA.symm i).property
    have htB : t j ∈ B := (eqB.symm (swapB j)).property
    exact Finset.disjoint_left.mp hAB hsA (heq.symm ▸ htB)
  have hinj : Function.Injective (Sum.elim s t) :=
    Function.Injective.sumElim hs_inj ht_inj hst_ne
  have hsu : s iu = u := by simp [s, iu]
  have htv : t iu = v := by simp [t, swapB, iu, iv]
  obtain ⟨paths, _, hfull⟩ := hG s t hinj
  let p : G.Walk u v := (paths iu).copy hsu htv
  have hp_avoid : ∀ x ∈ p.support, x ∉ S := by
    intro x hxp hxS
    let ix : Fin k := eqA ⟨x, hSA hxS⟩
    have hsx : s ix = x := by simp [s, ix]
    have hix : iu ≠ ix := by
      intro heq
      have : u = x := by rw [← hsu, ← hsx, heq]
      exact huS (this ▸ hxS)
    have hxpi : x ∈ (paths iu).support := by
      simpa [p] using hxp
    have hxpj : x ∈ (paths ix).support := by
      simpa [hsx] using (paths ix).start_mem_support
    exact Set.disjoint_left.mp (hfull iu ix hix) hxpi hxpj
  apply hnr
  have hp_compl : ∀ x ∈ p.support, x ∈ ((S : Set V)ᶜ) := by
    intro x hx
    exact hp_avoid x hx
  exact ⟨Walk.induce ((S : Set V)ᶜ) p hp_compl⟩

/-- **Every k-linked graph is `(2k - 1)`-connected** (Diestel §3.6,
Exercise 21).

For `k = 0` the claim is immediate.  Otherwise, if a separator `S` had fewer
than `2k - 1` vertices, choose `u` and `v` in different components of `G - S`.
Extend `S ∪ {u, v}` to a set of exactly `2k` terminals and enumerate it by
`Fin k ⊕ Fin k`, prescribing `u` and `v` as one paired source and target.
Every vertex of `S` is therefore a terminal of one of the other paths.  Full
support disjointness forces the `u`-`v` path to avoid all of `S`, contradicting
the choice of components. -/
theorem IsKLinkedStrong.isKConnected_two_mul_sub_one
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKLinkedStrong k)
    (hcard : 2 * k ≤ Fintype.card V) :
    G.IsKConnected (2 * k - 1) := by
  classical
  by_cases hk : k = 0
  · subst k
    exact Nat.zero_le _
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_contra hnot
  have htarget_card : (2 * k - 1) + 1 ≤ Fintype.card V := by omega
  obtain ⟨S, hScard, hSsep⟩ :=
    G.not_isKConnected_extract htarget_card hnot
  have hSlt : S.card < Fintype.card V := by omega
  have hcompl_nonempty : ((↑S : Set V))ᶜ.Nonempty := by
    obtain ⟨u, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hSlt
    exact ⟨u, by simpa using hu⟩
  obtain ⟨C₁, C₂, hCne⟩ := hSsep.exists_two_distinct_components hcompl_nonempty
  obtain ⟨⟨u, huS⟩, huC⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₁ := C₁.exists_rep
  obtain ⟨⟨v, hvS⟩, hvC⟩ : ∃ x : (((S : Set V))ᶜ : Set V),
      (G.induce ((S : Set V)ᶜ)).connectedComponentMk x = C₂ := C₂.exists_rep
  have huv : u ≠ v := by
    intro huv
    apply hCne
    rw [← huC, ← hvC]
    exact congrArg _ (Subtype.ext huv)
  have hnr : ¬ (G.induce ((S : Set V)ᶜ)).Reachable ⟨u, huS⟩ ⟨v, hvS⟩ := by
    intro hreach
    apply hCne
    rw [← huC, ← hvC]
    exact (SimpleGraph.ConnectedComponent.eq).mpr hreach

  let base : Finset V := S ∪ {u, v}
  have hbase_card : base.card ≤ 2 * k := by
    calc
      base.card ≤ S.card + ({u, v} : Finset V).card := by
        simpa only [base] using Finset.card_union_le S {u, v}
      _ ≤ 2 * k := by
        have hpairs : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
  obtain ⟨E, hbaseE, _hEuniv, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ base) hbase_card hcard
  have huE : u ∈ E := hbaseE (by simp [base])
  have hvE : v ∈ E := hbaseE (by simp [base])
  have hSE : S ⊆ E := fun x hx => hbaseE (by simp [base, hx])

  let i0 : Fin k := ⟨0, hkpos⟩
  let anchors : Finset (Fin k ⊕ Fin k) := {Sum.inl i0, Sum.inr i0}
  let endpoint : Fin k ⊕ Fin k → V := Sum.elim (fun _ => u) (fun _ => v)
  have hanchor_image : anchors.image endpoint ⊆ E := by
    intro x hx
    simp only [anchors, endpoint, Finset.image_insert, Finset.image_singleton,
      Sum.elim_inl, Sum.elim_inr, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huE
    · exact hvE
  have hanchor_inj : Set.InjOn endpoint anchors := by
    intro a ha b hb hab
    simp only [anchors, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hab huv
    · exact absurd hab.symm huv
    · rfl
  have hdomain_card : Fintype.card (Fin k ⊕ Fin k) = E.card := by
    simp [hEcard, two_mul]
  obtain ⟨q, hq⟩ := Finset.exists_equiv_extend_of_card_eq
    hdomain_card hanchor_image hanchor_inj
  let s : Fin k → V := fun i => (q (Sum.inl i)).val
  let t : Fin k → V := fun i => (q (Sum.inr i)).val
  have hinj : Function.Injective (Sum.elim s t) := by
    intro a b hab
    apply q.injective
    apply Subtype.ext
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  have hsu : s i0 = u := by
    simpa [s, endpoint] using hq (Sum.inl i0) (by simp [anchors])
  have htv : t i0 = v := by
    simpa [t, endpoint] using hq (Sum.inr i0) (by simp [anchors])
  obtain ⟨paths, _, hfull⟩ := hG s t hinj
  let p : G.Walk u v := (paths i0).copy hsu htv

  let slot : S → Fin k ⊕ Fin k := fun x =>
    q.symm ⟨x.val, hSE x.property⟩
  have hp_avoid : ∀ x ∈ p.support, x ∉ S := by
    intro x hxp hxS
    let xs : S := ⟨x, hxS⟩
    let d : Fin k ⊕ Fin k := slot xs
    have hqd : q d = (⟨x, hSE hxS⟩ : E) := by
      exact q.apply_symm_apply _
    have hdx : (q d).val = x := congrArg Subtype.val hqd
    have hdu : d ≠ Sum.inl i0 := by
      intro hd
      have hqu := hq (Sum.inl i0) (by simp [anchors])
      have hxu : x = u := by
        rw [← hdx, hd]
        simpa [endpoint] using hqu
      exact huS (hxu ▸ hxS)
    have hdv : d ≠ Sum.inr i0 := by
      intro hd
      have hqv := hq (Sum.inr i0) (by simp [anchors])
      have hxv : x = v := by
        rw [← hdx, hd]
        simpa [endpoint] using hqv
      exact hvS (hxv ▸ hxS)
    have hxpi : x ∈ (paths i0).support := by
      simpa [p] using hxp
    rcases d with j | j
    · have hji : i0 ≠ j := by
        intro hij
        exact hdu (congrArg Sum.inl hij.symm)
      have hsjx : s j = x := hdx
      have hxpj : x ∈ (paths j).support := by
        simpa [hsjx] using (paths j).start_mem_support
      exact Set.disjoint_left.mp (hfull i0 j hji) hxpi hxpj
    · have hji : i0 ≠ j := by
        intro hij
        exact hdv (congrArg Sum.inr hij.symm)
      have htjx : t j = x := hdx
      have hxpj : x ∈ (paths j).support := by
        simpa [htjx] using (paths j).end_mem_support
      exact Set.disjoint_left.mp (hfull i0 j hji) hxpi hxpj
  apply hnr
  exact ⟨Walk.induce ((S : Set V)ᶜ) p (fun x hx => hp_avoid x hx)⟩

/-- Book-faithful linkedness is monotone in its order: a `k`-linked graph is
`j`-linked for every `j ≤ k`, provided the ambient graph has the `2k`
vertices required by the textbook convention.

Given any `2j` distinct prescribed terminals, extend their image to a set of
exactly `2k` vertices.  An equivalence `Fin k ⊕ Fin k ≃ E` is chosen to agree
with the original terminals on the embedded `Fin j ⊕ Fin j`; apply the
`k`-linkage and retain the first `j` paths.  Copying their endpoint indices
does not change support, so pairwise disjointness of full supports is
preserved.  The case `j = 0` is handled directly. -/
theorem IsKLinkedStrong.le {G : SimpleGraph V} {j k : Nat}
    (hcard : 2 * k ≤ Fintype.card V) (hjk : j ≤ k)
    (hG : G.IsKLinkedStrong k) : G.IsKLinkedStrong j := by
  classical
  intro s t hinj
  by_cases hj0 : j = 0
  · subst j
    refine ⟨fun i => i.elim0, ?_, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  let j0 : Fin j := ⟨0, hjpos⟩
  let emb : Fin j ⊕ Fin j → Fin k ⊕ Fin k :=
    Sum.map (Fin.castLE hjk) (Fin.castLE hjk)
  have hemb_inj : Function.Injective emb := by
    exact (Fin.castLE_injective hjk).sumMap (Fin.castLE_injective hjk)
  let terminals : Finset V :=
    (Finset.univ : Finset (Fin j ⊕ Fin j)).image (Sum.elim s t)
  have hterm_card : terminals.card = 2 * j := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [two_mul]
  have hterm_le : terminals.card ≤ 2 * k := by
    rw [hterm_card]
    omega
  obtain ⟨E, htermE, _hEuniv, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq
      (Finset.subset_univ terminals) hterm_le hcard
  let endpoint : Fin k ⊕ Fin k → V :=
    Function.extend emb (Sum.elim s t) (fun _ => s j0)
  have hemb_apply (a : Fin j ⊕ Fin j) :
      endpoint (emb a) = Sum.elim s t a := by
    exact hemb_inj.extend_apply (Sum.elim s t) (fun _ => s j0) a
  let anchors : Finset (Fin k ⊕ Fin k) :=
    (Finset.univ : Finset (Fin j ⊕ Fin j)).image emb
  have hanchor_image : anchors.image endpoint ⊆ E := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨a, _, rfl⟩
    apply htermE
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, (hemb_apply a).symm⟩
  have hanchor_inj : Set.InjOn endpoint anchors := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, _, rfl⟩
    apply congrArg emb
    apply hinj
    simpa only [hemb_apply] using hab
  have hdomain_card : Fintype.card (Fin k ⊕ Fin k) = E.card := by
    simp [hEcard, two_mul]
  obtain ⟨q, hq⟩ := Finset.exists_equiv_extend_of_card_eq
    hdomain_card hanchor_image hanchor_inj
  let s' : Fin k → V := fun i => (q (Sum.inl i)).val
  let t' : Fin k → V := fun i => (q (Sum.inr i)).val
  have hinj' : Function.Injective (Sum.elim s' t') := by
    intro a b hab
    apply q.injective
    apply Subtype.ext
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  have hs (i : Fin j) : s' (Fin.castLE hjk i) = s i := by
    have hanchor : emb (Sum.inl i) ∈ anchors := by
      exact Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
    change (q (Sum.inl (Fin.castLE hjk i))).val = s i
    calc
      _ = endpoint (emb (Sum.inl i)) := by
        simpa [emb] using hq (emb (Sum.inl i)) hanchor
      _ = Sum.elim s t (Sum.inl i) := hemb_apply (Sum.inl i)
      _ = s i := rfl
  have ht (i : Fin j) : t' (Fin.castLE hjk i) = t i := by
    have hanchor : emb (Sum.inr i) ∈ anchors := by
      exact Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, rfl⟩
    change (q (Sum.inr (Fin.castLE hjk i))).val = t i
    calc
      _ = endpoint (emb (Sum.inr i)) := by
        simpa [emb] using hq (emb (Sum.inr i)) hanchor
      _ = Sum.elim s t (Sum.inr i) := hemb_apply (Sum.inr i)
      _ = t i := rfl
  obtain ⟨paths, hpaths, hfull⟩ := hG s' t' hinj'
  let smallPaths : ∀ i : Fin j, G.Walk (s i) (t i) := fun i =>
    (paths (Fin.castLE hjk i)).copy (hs i) (ht i)
  refine ⟨smallPaths, ?_, ?_⟩
  · intro i
    change ((paths (Fin.castLE hjk i)).copy (hs i) (ht i)).IsPath
    rw [Walk.isPath_copy]
    exact hpaths (Fin.castLE hjk i)
  · intro i l hil
    have hcast_ne : Fin.castLE hjk i ≠ Fin.castLE hjk l := by
      exact (Fin.castLE_injective hjk).ne hil
    simpa only [smallPaths, Walk.support_copy] using
      hfull (Fin.castLE hjk i) (Fin.castLE hjk l) hcast_ne

end IsKLinkedStrongImpKConnected

end SimpleGraph
