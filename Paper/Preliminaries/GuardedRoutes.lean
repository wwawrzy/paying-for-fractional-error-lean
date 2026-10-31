import Paper.Preliminaries.DeletionComponents

/-! Transfer connectivity through actual physical edge walks. Every vertex
on an edge route carries at least one of the two endpoint labels. -/
namespace Paper.GuardedRoutes
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable (K : SimpleGraph A) (G : SimpleGraph B)

structure System where
  root : A → B
  injective : Function.Injective root
  labels : B → Finset A
  root_label : ∀ a, a ∈ labels (root a)
  route : ∀ {a b}, K.Adj a b → G.Walk (root a) (root b)
  guarded : ∀ {a b} (h : K.Adj a b), ∀ v ∈ (route h).support, a ∈ labels v ∨ b ∈ labels v

variable {K G}

noncomputable def cut (S : System K G) (Z : Finset B) : Finset A := Z.biUnion S.labels

theorem root_avoids (S : System K G) (Z : Finset B) {a : A} (ha : a ∉ cut S Z) : S.root a ∉ Z := by
  intro hz
  exact ha (Finset.mem_biUnion.mpr ⟨S.root a, hz, S.root_label a⟩)

theorem route_avoids (S : System K G) (Z : Finset B) {a b : A} (h : K.Adj a b)
    (ha : a ∉ cut S Z) (hb : b ∉ cut S Z) : ∀ v ∈ (S.route h).support, v ∉ Z := by
  intro v hv hz
  rcases S.guarded h v hv with hlabel | hlabel
  · exact ha (Finset.mem_biUnion.mpr ⟨v, hz, hlabel⟩)
  · exact hb (Finset.mem_biUnion.mpr ⟨v, hz, hlabel⟩)

noncomputable def rootAfter (S : System K G) (Z : Finset B) (a : {a // a ∉ cut S Z}) : {b // b ∉ Z} :=
  ⟨S.root a.val, root_avoids S Z a.property⟩

theorem edge_reachable (S : System K G) (Z : Finset B) {a b : {a // a ∉ cut S Z}}
    (h : (K.induce {a | a ∉ cut S Z}).Adj a b) :
    (G.induce {b | b ∉ Z}).Reachable (rootAfter S Z a) (rootAfter S Z b) :=
  ((S.route h).induce {b | b ∉ Z} (route_avoids S Z h a.property b.property)).reachable

theorem reachable (S : System K G) (Z : Finset B) {a b : {a // a ∉ cut S Z}}
    (h : (K.induce {a | a ∉ cut S Z}).Reachable a b) :
    (G.induce {b | b ∉ Z}).Reachable (rootAfter S Z a) (rootAfter S Z b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih => exact (edge_reachable S Z h).trans ih

theorem cut_card (S : System K G) (Z : Finset B) (L : ℕ) (hL : ∀ v, (S.labels v).card ≤ L) :
    (cut S Z).card ≤ L * Z.card := by
  calc
    _ ≤ ∑ v ∈ Z, (S.labels v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Z, L := Finset.sum_le_sum (fun v _ => hL v)
    _ = _ := by simp [mul_comm]
end Paper.GuardedRoutes
