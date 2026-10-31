import Paper.Certificates.Counting.ApproximateOrientation

/-! Ordered endpoint counts of a finite copied-edge orientation. -/
namespace Paper.OrientationShares
open ApproximateOrientation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {q : Nat} (O : MultiOrientation G q)

noncomputable def other (e : G.edgeFinset × Fin q) : V := Sym2.Mem.other (O.incident e)

theorem edge_eq (e : G.edgeFinset × Fin q) :
    s(O.tail e, other G O e) = e.1.val := Sym2.other_spec (O.incident e)

theorem endpoints_adj (e : G.edgeFinset × Fin q) : G.Adj (O.tail e) (other G O e) := by
  have h := SimpleGraph.mem_edgeFinset.mp e.1.prop
  rw [← edge_eq G O e] at h
  exact h

noncomputable def copies (u v : V) : Finset (G.edgeFinset × Fin q) := by
  classical
  exact Finset.univ.filter (fun e => O.tail e = v ∧ other G O e = u)

noncomputable def count (u v : V) : Nat := (copies G O u v).card

theorem count_zero (u v : V) (h : ¬ G.Adj u v) : count G O u v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_,ht,ho⟩ := Finset.mem_filter.mp he
  exact h (by simpa only [ht,ho] using (endpoints_adj G O e).symm)

theorem sum_count (v : V) : (∑ u, count G O u v) = load G O v := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun e => O.tail e = v))
    (t := (Finset.univ : Finset V)) (f := other G O)
    (fun _ _ => Finset.mem_univ _)
  simpa only [count,copies,load,Finset.filter_filter] using hh.symm

theorem sum_load : (∑ v, load G O v) = q * G.edgeFinset.card := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (G.edgeFinset × Fin q)))
    (t := (Finset.univ : Finset V)) (f := O.tail)
    (fun _ _ => Finset.mem_univ _)
  simpa [load,Fintype.card_prod,mul_comm] using hh.symm

theorem pair_count (u v : V) (huv : G.Adj u v) :
    count G O u v + count G O v u = q := by
  classical
  let edge : G.edgeFinset := ⟨s(u,v), SimpleGraph.mem_edgeFinset.mpr huv⟩
  have hsets : copies G O u v ∪ copies G O v u =
      ({edge} ×ˢ (Finset.univ : Finset (Fin q))) := by
    ext e
    simp only [copies,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_product,Finset.mem_singleton,and_true]
    constructor
    · rintro (⟨ht,ho⟩ | ⟨ht,ho⟩)
      · apply Subtype.ext
        change e.1.val = s(u,v)
        rw [← edge_eq G O e,ht,ho,Sym2.eq_swap]
      · apply Subtype.ext
        change e.1.val = s(u,v)
        rw [← edge_eq G O e,ht,ho]
    · intro he
      have he' : e.1.val = s(u,v) := congrArg Subtype.val he
      have ht := O.incident e
      rw [he',Sym2.mem_iff] at ht
      rcases ht with ht | ht
      · right
        refine ⟨ht,?_⟩
        apply Sym2.congr_right.mp
        simpa only [ht,he'] using edge_eq G O e
      · left
        refine ⟨ht,?_⟩
        apply Sym2.congr_right.mp
        simpa only [ht,he',Sym2.eq_swap] using edge_eq G O e
  have hd : Disjoint (copies G O u v) (copies G O v u) := by
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    have h1' := (Finset.mem_filter.mp h1).2.1
    have h2' := (Finset.mem_filter.mp h2).2.1
    exact (G.ne_of_adj huv) (h2'.symm.trans h1')
  have hh := congrArg Finset.card hsets
  rw [Finset.card_union_of_disjoint hd] at hh
  simpa [count] using hh

end Paper.OrientationShares
#print axioms Paper.OrientationShares.endpoints_adj
#print axioms Paper.OrientationShares.sum_count
#print axioms Paper.OrientationShares.sum_load

namespace Paper.OrientationShares
open ApproximateOrientation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {q : Nat} (O : MultiOrientation G q)
noncomputable def share (u v : V) : ℝ := count G O u v / q

theorem share_nonneg (u v : V) : 0 ≤ share G O u v := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem share_zero (u v : V) (h : ¬ G.Adj u v) : share G O u v = 0 := by
  simp only [share,count_zero G O u v h,Nat.cast_zero,zero_div]

theorem share_pair (hq : 0 < q) (u v : V) (huv : G.Adj u v) :
    share G O u v + share G O v u = 1 := by
  have hh := pair_count G O u v huv
  have hh' : (count G O u v : ℝ) + count G O v u = q := by exact_mod_cast hh
  rw [share,share,← add_div,hh',div_self (by exact_mod_cast (Nat.ne_of_gt hq))]

theorem share_load (v : V) : (∑ u, share G O u v) = (load G O v : ℝ) / q := by
  simp only [share,← Finset.sum_div,← Nat.cast_sum,sum_count]

end Paper.OrientationShares
#print axioms Paper.OrientationShares.pair_count
#print axioms Paper.OrientationShares.share_pair
#print axioms Paper.OrientationShares.share_load
