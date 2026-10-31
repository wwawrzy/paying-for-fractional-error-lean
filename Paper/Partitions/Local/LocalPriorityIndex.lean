import Paper.Partitions.Local.BoundedBall

/-! Canonical bounded local priority coordinates: minimum identifier and
the membership mask in its sorted original radius-k ball, padded to B.
This uses only that ball, rather than a global enumeration of vertex sets. -/
namespace Paper.LocalPriorityIndex
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def mask (v : V) (k B : ℕ) (S : Finset V) (i : Fin B) : Bool :=
  if hi : i.val < (BoundedBall.ball G v k).card then
    decide ((BoundedBall.ball G v k).orderEmbOfFin rfl ⟨i.val, hi⟩ ∈ S)
  else false

theorem mask_injective (v : V) (k B : ℕ) (hB : (BoundedBall.ball G v k).card ≤ B)
    (S T : Finset V) (hS : S ⊆ BoundedBall.ball G v k) (hT : T ⊆ BoundedBall.ball G v k)
    (he : mask G v k B S = mask G v k B T) : S = T := by
  ext u
  by_cases hu : u ∈ BoundedBall.ball G v k
  · let j := ((BoundedBall.ball G v k).orderIsoOfFin rfl).symm ⟨u, hu⟩
    let i : Fin B := ⟨j.val, j.isLt.trans_le hB⟩
    have hj : (BoundedBall.ball G v k).orderEmbOfFin rfl j = u :=
      congrArg Subtype.val (((BoundedBall.ball G v k).orderIsoOfFin rfl).apply_symm_apply ⟨u, hu⟩)
    have hh := congrFun he i
    have hi : i.val < (BoundedBall.ball G v k).card := j.isLt
    have hj' : (BoundedBall.ball G v k).orderEmbOfFin rfl ⟨i.val, hi⟩ = u := hj
    simpa only [mask, dif_pos hi, hj', decide_eq_decide] using hh
  · exact ⟨fun hv => False.elim (hu (hS hv)), fun hv => False.elim (hu (hT hv))⟩

def Domain (k : ℕ) := {S : Finset V // (G.induce (S : Set V)).Connected ∧ S.card ≤ k}

theorem nonempty (k : ℕ) (S : Domain G k) : S.val.Nonempty := by
  obtain ⟨v⟩ := S.property.1.nonempty
  exact ⟨v.val, v.property⟩

noncomputable def leader (k : ℕ) (S : Domain G k) : V := S.val.min' (nonempty G k S)

theorem leader_mem (k : ℕ) (S : Domain G k) : leader G k S ∈ S.val := Finset.min'_mem _ _

noncomputable def index (Δ k : ℕ) (S : Domain G k) : V × (Fin ((Δ + 1) ^ k) → Bool) :=
  (leader G k S, mask G (leader G k S) k ((Δ + 1) ^ k) S.val)

theorem injective (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) :
    Function.Injective (index G Δ k) := by
  intro S T he
  have hl : leader G k S = leader G k T := congrArg Prod.fst he
  have hm := congrArg Prod.snd he
  change mask G (leader G k S) k ((Δ + 1) ^ k) S.val =
    mask G (leader G k T) k ((Δ + 1) ^ k) T.val at hm
  rw [← hl] at hm
  have hS := BoundedBall.contains_connected G S.val S.property.1 k S.property.2 _ (leader_mem G k S)
  have hT := BoundedBall.contains_connected G T.val T.property.1 k T.property.2 _ (leader_mem G k T)
  rw [← hl] at hT
  exact Subtype.ext (mask_injective G _ k _ (BoundedBall.card_bound G Δ hdeg _ k) S.val T.val hS hT hm)
end Paper.LocalPriorityIndex
