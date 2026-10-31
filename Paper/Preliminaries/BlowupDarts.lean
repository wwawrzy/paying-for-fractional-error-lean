import Paper.Preliminaries.BlowupEdge
import Paper.Averaging.Tasks.FiniteIncidenceAverage

/-! Pointwise and averaged counts of shallow-minor darts whose physical
roots differ. Every counted outcome uses the actual projected star minor. -/
namespace Paper.BlowupDarts
attribute [local instance] Classical.propDecidable
open BlowupProjection BlowupEdge
open scoped BigOperators
universe u
variable {V A : Type u} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {c : ℕ}
variable {J : SimpleGraph A} [DecidableRel J.Adj] (M : DepthOne.StarModel J (blowup G c))

noncomputable def alive (ω : V → Fin c) : Finset J.Dart :=
  Finset.univ.filter (fun d => Survives M ω d.fst d.snd)

noncomputable def separated : Finset J.Dart :=
  Finset.univ.filter (fun d => (M.root d.fst).1 ≠ (M.root d.snd).1)

theorem alive_card (ω : V → Fin c) : (alive M ω).card ≤ 2 * (graph M ω).edgeFinset.card := by
  classical
  let f : (alive M ω) → (graph M ω).Dart := fun d => {
    toProd := (⟨d.val.fst, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp d.property).2.1⟩⟩,
      ⟨d.val.snd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp d.property).2.2.1⟩⟩)
    adj := ⟨fun he => d.val.adj.ne (congrArg Subtype.val he), (Finset.mem_filter.mp d.property).2.2.2⟩ }
  have hinj : Function.Injective f := by
    intro d e he
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact congrArg (fun z : (graph M ω).Dart => z.fst.val) he
    · exact congrArg (fun z : (graph M ω).Dart => z.snd.val) he
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, SimpleGraph.dart_card_eq_twice_card_edges] using hc

theorem separated_density (hc : 1 ≤ c) {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) :
    ((separated M).card : ℝ) ≤ (c : ℝ) ^ 4 * (2 * a * Fintype.card A) := by
  classical
  let W : Finset (V → Fin c) := Finset.univ
  have hW : W.Nonempty := ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
  rw [← Nat.cast_pow]
  apply FiniteIncidenceAverage.bound (separated M) W hW
    (fun d ω => Survives M ω d.fst d.snd) (c ^ 4) (2 * a * Fintype.card A)
  · intro d hd
    have hp := (Finset.mem_filter.mp hd).2
    obtain ⟨F, hF, target, htarget⟩ := cylinder_survives M d.adj hp
    have hs : FiniteCylinder.cylinder F target ⊆ W.filter (fun ω => Survives M ω d.fst d.snd) := by
      intro ω hω
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htarget ω hω⟩
    have hh := FiniteCylinder.bounded_coordinates F target 4 hc hF
    have hh' : W.card ≤ c ^ 4 * (FiniteCylinder.cylinder F target).card := by
      simpa only [W, Finset.card_univ] using hh
    exact hh'.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hs))
  · intro ω _
    have hs : (separated M).filter (fun d => Survives M ω d.fst d.snd) ⊆ alive M ω := by
      intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩
    have hl := (Finset.card_le_card hs).trans (alive_card M ω)
    have hl' : (((separated M).filter (fun d => Survives M ω d.fst d.snd)).card : ℝ) ≤
        2 * ((graph M ω).edgeFinset.card : ℝ) := by exact_mod_cast hl
    have hh := outcome_density M hden ha ω
    nlinarith
end Paper.BlowupDarts
