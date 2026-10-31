import Paper.Preliminaries.PacketCode

/-! A computable code for a fixed finite counter. Its width depends only
on the counter bound, never on the order or topology of the input graph. -/
namespace Paper.SmallNumberCode
open BroadcastModel

def code (m : ℕ) : BitCode (Fin m) m := PacketCode.ofInverse
  (fun i j => decide (i = j))
  (fun bits => ((Finset.univ.filter (fun i => bits i = true)).sort (· ≤ ·)).head?)
  (by
    intro i
    have he : (Finset.univ.filter (fun j : Fin m => decide (i = j) = true)) = {i} := by
      ext j
      simp [eq_comm]
    dsimp only
    rw [he]
    simp)
end Paper.SmallNumberCode
