import Paper.Preliminaries.BlowupDarts

/-! A fully finite transfer of depth-one density through a clique blowup.
We obtain the sufficient bound a*c^4+c. No all-minors density of a blowup
is assumed or asserted. -/
namespace Paper.BlowupDensity
attribute [local instance] Classical.propDecidable
open BlowupProjection BlowupDarts
universe u
variable {V A : Type u} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ}
variable {J : SimpleGraph A} [DecidableRel J.Adj] (M : DepthOne.StarModel J (blowup G c))

theorem root_injective : Function.Injective M.root := by
  intro a b he
  by_contra hn
  exact Set.disjoint_left.mp (M.disjoint a b hn) (M.root_mem a) (he.symm ▸ M.root_mem b)

noncomputable def coincident : Finset J.Dart :=
  Finset.univ.filter (fun d => (M.root d.fst).1 = (M.root d.snd).1)

theorem coincident_card : (coincident M).card ≤ c * Fintype.card A := by
  classical
  let f : (coincident M) → A × Fin c := fun d => (d.val.fst, (M.root d.val.snd).2)
  have hinj : Function.Injective f := by
    intro d e he
    have hf : d.val.fst = e.val.fst := congrArg (fun p : A × Fin c => p.1) he
    have hs : (M.root d.val.snd).2 = (M.root e.val.snd).2 := congrArg (fun p : A × Fin c => p.2) he
    have hd := (Finset.mem_filter.mp d.property).2
    have he' := (Finset.mem_filter.mp e.property).2
    have hr : M.root d.val.snd = M.root e.val.snd :=
      Prod.ext (hd.symm.trans ((congrArg (fun a => (M.root a).1) hf).trans he')) hs
    apply Subtype.ext
    exact SimpleGraph.Dart.ext _ _ (Prod.ext hf (root_injective M hr))
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, mul_comm] using hc

include M in
theorem model_density (hc : 1 ≤ c) {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) :
    (J.edgeFinset.card : ℝ) ≤ (a * (c : ℝ) ^ 4 + c) * Fintype.card A := by
  classical
  have hsep := separated_density M hc hden ha
  have hbad := coincident_card M
  have hbad' : ((coincident M).card : ℝ) ≤ (c : ℝ) * Fintype.card A := by exact_mod_cast hbad
  have he : (separated M).card + (coincident M).card = 2 * J.edgeFinset.card := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset J.Dart))
      (fun d => (M.root d.fst).1 ≠ (M.root d.snd).1)
    simpa only [separated, coincident, not_not, Finset.card_univ, SimpleGraph.dart_card_eq_twice_card_edges] using hh
  have he' : ((separated M).card : ℝ) + (coincident M).card = 2 * (J.edgeFinset.card : ℝ) := by exact_mod_cast he
  have hn : (0 : ℝ) ≤ (c : ℝ) * Fintype.card A := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith

theorem bound (hc : 1 ≤ c) {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) :
    DepthOne.Bound (blowup G c) (a * (c : ℝ) ^ 4 + c) := by
  intro A _ _ J _ M
  exact model_density M hc hden ha
end Paper.BlowupDensity
