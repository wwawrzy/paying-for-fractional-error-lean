import Paper.Partitions.Local.FinitePriorityIndex

/-! Executable decoding of subset masks in a finite sorted address list.
Canonical padding is checked explicitly to avoid duplicate task roles. -/
namespace Paper.FiniteSubsetCode
variable {V : Type} [LinearOrder V]

def encode (l : List V) (B : ℕ) (S : Finset V) (i : Fin B) : Bool :=
  if hi : i.val < l.length then decide (l.get ⟨i.val, hi⟩ ∈ S) else false

def selected (l : List V) (B : ℕ) (ω : Fin B → Bool) (i : Fin l.length) : Bool :=
  if hi : i.val < B then ω ⟨i.val, hi⟩ else false

def decode (l : List V) (B : ℕ) (ω : Fin B → Bool) : Finset V :=
  (Finset.univ.filter (fun i : Fin l.length => selected l B ω i)).image l.get

theorem selected_encode (l : List V) (B : ℕ) (hB : l.length ≤ B) (S : Finset V)
    (i : Fin l.length) : selected l B (encode l B S) i = decide (l.get i ∈ S) := by
  have hi : i.val < B := lt_of_lt_of_le i.isLt hB
  simp only [selected, dif_pos hi, encode, dif_pos i.isLt]

theorem decode_subset (l : List V) (B : ℕ) (ω : Fin B → Bool) :
    decode l B ω ⊆ l.toFinset := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact List.mem_toFinset.mpr (List.get_mem _ _)

theorem mem_decode_encode (l : List V) (B : ℕ) (hB : l.length ≤ B)
    (S : Finset V) (v : V) :
    v ∈ decode l B (encode l B S) ↔ v ∈ l.toFinset ∧ v ∈ S := by
  simp only [decode, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    selected_encode l B hB S, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨List.mem_toFinset.mpr (List.get_mem _ _), hi⟩
  · rintro ⟨hl, hv⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hl)
    exact ⟨i, hi.symm ▸ hv, hi⟩

theorem decode_encode (l : List V) (B : ℕ) (hB : l.length ≤ B)
    (S : Finset V) (hS : S ⊆ l.toFinset) : decode l B (encode l B S) = S := by
  ext v
  rw [mem_decode_encode l B hB S v]
  exact ⟨And.right, fun hv => ⟨hS hv, hv⟩⟩

theorem encode_injective (l : List V) (B : ℕ) (hB : l.length ≤ B)
    (S T : Finset V) (hS : S ⊆ l.toFinset) (hT : T ⊆ l.toFinset)
    (he : encode l B S = encode l B T) : S = T := by
  rw [← decode_encode l B hB S hS, ← decode_encode l B hB T hT, he]

theorem encode_ball (N : V → Finset V) (a : V) (k B : ℕ) (S : Finset V) :
    encode ((NeighborBalls.ball N a k).sort (· ≤ ·)) B S = FinitePriorityIndex.mask N a k B S := by
  funext i
  unfold encode FinitePriorityIndex.mask
  simp only [Finset.length_sort, List.get_eq_getElem]

theorem canonical_mask_unique (l : List V) (B : ℕ) (S : Finset V)
    (ω : Fin B → Bool) (hc : ω = encode l B (decode l B ω)) (hS : decode l B ω = S) :
    ω = encode l B S := by rw [hc, hS]

end Paper.FiniteSubsetCode
