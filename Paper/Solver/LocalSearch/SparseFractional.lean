import Paper.Preliminaries.SparseParallelCorrect
import Paper.Solver.LocalSearch.MaskedFractionalSearch

/-! Actual sparse parallel fractional solver. Each role is routed only
through its own physical participants by the proved sparse compiler. -/
namespace Paper.SparseFractional
open BroadcastModel
variable {V Role : Type} [LinearOrder V] [LinearOrder Role]

def program {b c : ℕ} (C : BitCode V b) (R : BitCode Role c) (K D a B q M : ℕ) :=
  SparseParallel.execute R K (FractionalSearch.program C D a B q M)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem role_run {b c : ℕ} (C : BitCode V b) (R : BitCode Role c) (K D a B q M : ℕ)
    (xs : V → List (Role × FractionalSearch.Input V B))
    (hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ K)
    (s : V → Role → FractionalSearch.Input V B)
    (hs : ∀ v, TaggedDictionary.Consistent (s v) (xs v))
    (H : Finset V) (r : Role) (hr : ∀ v, r ∈ TaggedDictionary.keys (xs v) ↔ v ∈ H)
    (v : V) (hv : v ∈ H) :
    TaggedDictionary.lookup (((program C R K D a B q M).run G xs v).1) r =
      some ((FractionalSearch.program C D a B q M).run (MaskedTaskGraph.graph G H) (fun u => s u r) v) := by
  have he : SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r = H := by
    ext u
    rw [SparseRolePrepare.mem_vertices, hr u]
  have hh := SparseParallelCorrect.execute_correct G R K (FractionalSearch.program C D a B q M)
    xs hK s hs v r ((hr v).mpr hv)
  rw [he] at hh
  exact hh

theorem key_run {b c : ℕ} (C : BitCode V b) (R : BitCode Role c) (K D a B q M : ℕ)
    (xs : V → List (Role × FractionalSearch.Input V B))
    (hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ K)
    (s : V → Role → FractionalSearch.Input V B) (hs : ∀ v, TaggedDictionary.Consistent (s v) (xs v))
    (v : V) (r : Role) (hr : r ∈ TaggedDictionary.keys (xs v)) :
    TaggedDictionary.lookup (((program C R K D a B q M).run G xs v).1) r =
      some ((FractionalSearch.program C D a B q M).run
        (MaskedTaskGraph.graph G (SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r))
        (fun u => s u r) v) :=
  SparseParallelCorrect.execute_correct G R K (FractionalSearch.program C D a B q M) xs hK s hs v r hr

theorem rounds {b c : ℕ} (C : BitCode V b) (R : BitCode Role c) (K D a B q M : ℕ) :
    (program C R K D a B q M).rounds = 1 + (FractionalSearch.program C D a B q M).rounds :=
  SparseParallel.execute_rounds R K _

theorem maxBits {b c : ℕ} (C : BitCode V b) (R : BitCode Role c) (K D a B q M : ℕ) :
    (program C R K D a B q M).maxBits ≤ K * (c + (FractionalSearch.program C D a B q M).maxBits + 1) :=
  SparseParallel.execute_maxBits R K _
end Paper.SparseFractional
