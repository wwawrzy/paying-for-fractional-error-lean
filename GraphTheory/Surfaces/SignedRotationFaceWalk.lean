import GraphTheory.Surfaces.SignedRotationCorners
namespace SimpleGraph.SignedRotation
variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
def faceStep (x : Flag G) : Flag G := r.cornerFlip (r.edgeFlip x)
def faceStepInverse (x : Flag G) : Flag G := r.edgeFlip (r.cornerFlip x)

theorem faceStep_left_inverse : Function.LeftInverse r.faceStepInverse r.faceStep := by
  intro x
  change r.edgeFlip (r.cornerFlip (r.cornerFlip (r.edgeFlip x))) = x
  rw [r.cornerFlip_involutive (r.edgeFlip x),r.edgeFlip_involutive x]

theorem faceStep_right_inverse : Function.RightInverse r.faceStepInverse r.faceStep := by
  intro x
  change r.cornerFlip (r.edgeFlip (r.edgeFlip (r.cornerFlip x))) = x
  rw [r.edgeFlip_involutive (r.cornerFlip x),r.cornerFlip_involutive x]

def faceStepPerm : Equiv.Perm (Flag G) :=
  ⟨r.faceStep,r.faceStepInverse,r.faceStep_left_inverse,r.faceStep_right_inverse⟩

theorem faceStep_source (x : Flag G) : (r.faceStep x).1.fst = x.1.snd := r.cornerFlip_source _

theorem faceStep_no_backtrack [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (x : Flag G) :
    (r.faceStep (r.faceStep x)).1.fst ≠ x.1.fst := by
  rw [r.faceStep_source]
  intro h
  apply r.cornerFlip_dart_ne hdeg (r.edgeFlip x)
  exact Dart.ext _ _ (Prod.ext (r.cornerFlip_source _) h)

def faceWalk (x : Flag G) : (n : ℕ) → G.Walk x.1.fst ((r.faceStep^[n]) x).1.fst
  | 0 => Walk.nil
  | n+1 => by
    have ha : G.Adj x.1.fst (r.faceStep x).1.fst := by rw [r.faceStep_source]; exact x.1.adj
    simpa only [Function.iterate_succ_apply] using Walk.cons ha (faceWalk (r.faceStep x) n)

theorem faceWalk_length (x : Flag G) (n : ℕ) : (r.faceWalk x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [faceWalk,Walk.length_cons] using congrArg Nat.succ (ih (r.faceStep x))
theorem faceWalk_getVert (x : Flag G) (n i : ℕ) (hi : i ≤ n) :
    (r.faceWalk x n).getVert i = ((r.faceStep^[i]) x).1.fst := by
  induction n generalizing x i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => simp only [Walk.getVert_zero,Function.iterate_zero,Function.id_def]
    | succ i =>
      simpa only [faceWalk,Walk.getVert_cons_succ,Function.iterate_succ_apply] using
        ih (r.faceStep x) i (by omega)

theorem faceWalk_no_backtrack [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (x : Flag G) (n i : ℕ) (hi : i+2 ≤ n) :
    (r.faceWalk x n).getVert (i+2) ≠ (r.faceWalk x n).getVert i := by
  rw [r.faceWalk_getVert x n (i+2) hi,r.faceWalk_getVert x n i (by omega)]
  rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
  exact r.faceStep_no_backtrack hdeg _

theorem faceStep_ne_self (x : Flag G) : r.faceStep x ≠ x := by
  intro h
  have hh := congrArg (fun z : Flag G => z.1.fst) h
  change (r.faceStep x).1.fst = x.1.fst at hh
  rw [r.faceStep_source] at hh
  exact x.1.adj.ne hh.symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
noncomputable def facePeriod (x : Flag G) : ℕ := (r.faceStepPerm.cycleOf x).support.card

theorem facePeriod_pos (x : Flag G) : 0 < r.facePeriod x := by
  apply Finset.card_pos.mpr
  refine ⟨x,Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨Equiv.Perm.SameCycle.refl _ x,?_⟩⟩
  exact Equiv.Perm.mem_support.mpr (r.faceStep_ne_self x)

theorem faceStep_periodic (x : Flag G) : (r.faceStep^[r.facePeriod x]) x = x := by
  have h := r.faceStepPerm.pow_mod_card_support_cycleOf_self_apply
    (r.faceStepPerm.cycleOf x).support.card x
  simp only [Nat.mod_self,pow_zero,Equiv.Perm.one_apply] at h
  have he : (r.faceStepPerm ^ r.facePeriod x) x = x := h.symm
  simpa only [Equiv.Perm.coe_pow] using he

noncomputable def faceBoundaryWalk (x : Flag G) : G.Walk x.1.fst x.1.fst :=
  (r.faceWalk x (r.facePeriod x)).copy rfl (congrArg (fun z : Flag G => z.1.fst) (r.faceStep_periodic x))

theorem faceBoundaryWalk_length (x : Flag G) : (r.faceBoundaryWalk x).length = r.facePeriod x := by
  rw [faceBoundaryWalk,Walk.length_copy,r.faceWalk_length]

theorem faceWalk_isPath_before_min_return (n : ℕ)
    (hmin : ∀ m : ℕ, 0 < m → m < n → ∀ x : Flag G,
      ((r.faceStep^[m]) x).1.fst ≠ x.1.fst)
    (x : Flag G) (N : ℕ) (hN : N < n) : (r.faceWalk x N).IsPath := by
  apply (Walk.IsPath.getVert_injOn_iff _).mp
  intro i hi j hj he
  simp only [Set.mem_setOf_eq,r.faceWalk_length] at hi hj
  rw [r.faceWalk_getVert x N i hi,r.faceWalk_getVert x N j hj] at he
  have hno (a b : ℕ) (hab : a < b) (hb : b ≤ N)
      (heq : ((r.faceStep^[a]) x).1.fst = ((r.faceStep^[b]) x).1.fst) : False := by
    have hh := hmin (b-a) (by omega) (by omega) ((r.faceStep^[a]) x)
    apply hh
    rw [← Function.iterate_add_apply,Nat.sub_add_cancel hab.le]
    exact heq.symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hno i j h hj he
  · exact hno j i h hi he.symm

theorem exists_cycle_le_facePeriod (hdeg : ∀ v, 2 ≤ G.degree v) (base : Flag G) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length ≤ r.facePeriod base := by
  classical
  have hp : ∃ n : ℕ, 0 < n ∧ ∃ x : Flag G, ((r.faceStep^[n]) x).1.fst = x.1.fst :=
    ⟨r.facePeriod base,r.facePeriod_pos base,base,
      congrArg (fun z : Flag G => z.1.fst) (r.faceStep_periodic base)⟩
  let n := Nat.find hp
  have hnpos : 0 < n := (Nat.find_spec hp).1
  obtain ⟨y,hy⟩ := (Nat.find_spec hp).2
  change ((r.faceStep^[n]) y).1.fst = y.1.fst at hy
  have hmin : ∀ m : ℕ, 0 < m → m < n → ∀ x : Flag G,
      ((r.faceStep^[m]) x).1.fst ≠ x.1.fst := by
    intro m hm hmn x hx
    exact Nat.find_min hp hmn ⟨hm,x,hx⟩
  have hnle : n ≤ r.facePeriod base := Nat.find_min' hp
    ⟨r.facePeriod_pos base,base,congrArg (fun z : Flag G => z.1.fst) (r.faceStep_periodic base)⟩
  have hn1 : n ≠ 1 := by
    intro hn
    have hh : (r.faceStep y).1.fst = y.1.fst := by simpa only [hn,Function.iterate_one] using hy
    rw [r.faceStep_source] at hh
    exact y.1.adj.ne hh.symm
  have hn2 : n ≠ 2 := by
    intro hn
    apply r.faceStep_no_backtrack hdeg y
    simpa only [hn,Function.iterate_succ_apply',Function.iterate_zero,Function.id_def] using hy
  have hn3 : 3 ≤ n := by omega
  let p := r.faceWalk (r.faceStep y) (n-1)
  have he : ((r.faceStep^[n-1]) (r.faceStep y)).1.fst = y.1.fst := by
    rw [← Function.iterate_succ_apply]
    have hnsub : (n-1).succ = n := by omega
    rw [hnsub]
    exact hy
  have hpath : p.IsPath := r.faceWalk_isPath_before_min_return n hmin (r.faceStep y) (n-1) (by omega)
  have ha : G.Adj y.1.fst (r.faceStep y).1.fst := by rw [r.faceStep_source]; exact y.1.adj
  let w : G.Walk y.1.fst y.1.fst := Walk.cons ha (p.copy rfl he)
  have hw : w.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [w,Walk.isPath_def] using hpath
    · simp only [w,Walk.length_cons,Walk.length_copy,p,r.faceWalk_length]
      omega
  refine ⟨y.1.fst,w,hw,?_⟩
  have hl : w.length = n := by
    simp only [w,Walk.length_cons,Walk.length_copy,p,r.faceWalk_length]
    omega
  rw [hl]
  exact hnle

theorem facePeriod_ge_girth (hdeg : ∀ v, 2 ≤ G.degree v) (g : ℕ)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) (x : Flag G) :
    g ≤ r.facePeriod x := by
  obtain ⟨v,c,hc,hle⟩ := r.exists_cycle_le_facePeriod hdeg x
  exact (hg v c hc).trans hle

end SimpleGraph.SignedRotation





