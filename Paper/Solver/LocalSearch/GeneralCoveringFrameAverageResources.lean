import Paper.Solver.LocalSearch.GeneralCoveringInitializedFrameAverage

/-! Graph-independent round bounds and logarithmic broadcast widths for the
actual deterministic arbitrary-covering average. All coefficients below
depend only on public numeric parameters and the public ID-width constant. -/
namespace Paper.GeneralCoveringFrameAverageResources
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

def frameCoefficient (L Δ k n c : ℕ) : ℕ :=
  let r := GeneralCoveringOwnerFrameTaskInputs.outerRadius k n
  max ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
    (c + GeneralCoveringOwnerRootFrames.capacity Δ r * (c + Δ * (c + 1) + 1) + 1)

def solveCoefficient (a B k q c : ℕ) : ℕ :=
  3 * c + RecursiveSearch.extraBits (4 * k) a B q (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1

def taskCoefficient (L Δ a B k b n q c : ℕ) : ℕ :=
  max (frameCoefficient L Δ k n c)
    (GeneralCoveringOwnerFrameTaskInputs.capacity L Δ k b n *
      (c + GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n + solveCoefficient a B k q c + 1))

def coefficient (ifreq L Δ a B k b n q c : ℕ) : ℕ :=
  max (max (c + 1) (ifreq * (c + 1))) (max (taskCoefficient L Δ a B k b n q c) (c + 3))

theorem task_bits {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).maxBits ≤
      taskCoefficient L Δ a B k b n q c * Nat.clog 2 (N + 2) := by
  let H := Nat.clog 2 (N + 2)
  have hH : 1 ≤ H := Nat.clog_pos (by omega) (by omega)
  have hf : (GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).maxBits ≤
      frameCoefficient L Δ k n c * H := by
    rw [GeneralCoveringOwnerFrameTaskInputs.maxBits_eq]
    exact GeneralCoveringOwnerRoleFrames.logarithmic_bits I L Δ
      (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n) k (GeneralCoveringOwnerFrameTaskData.frameRadius k n) N c hids
  have hs := GeneralCoveringTaskFractionalSolve.logarithmic_bits I a B k q hB N c hids
  have hm : GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n ≤
      GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n * H := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n) hH
  have hsum : ids + GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n +
      (GeneralCoveringTaskFractionalSolve.program I a B k q hB).maxBits + 1 ≤
      (c + GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n + solveCoefficient a B k q c + 1) * H := by
    change _ ≤ _ * Nat.clog 2 (N + 2)
    dsimp only [solveCoefficient]
    dsimp only [H] at hm hH
    nlinarith
  apply (GeneralCoveringOwnerFrameFractional.maxBits I L Δ a B k t b n q hB).trans
  apply max_le
  · exact hf.trans (Nat.mul_le_mul_right H (le_max_left _ _))
  · have hb := Nat.mul_le_mul_left (GeneralCoveringOwnerFrameTaskInputs.capacity L Δ k b n) hsum
    calc
      _ ≤ (GeneralCoveringOwnerFrameTaskInputs.capacity L Δ k b n *
        (c + GeneralCoveringOwnerFrameTaskData.metadataCount Δ k b n + solveCoefficient a B k q c + 1)) * H := by
          simpa only [Nat.mul_assoc] using hb
      _ ≤ _ := Nat.mul_le_mul_right H (le_max_right _ _)

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (GeneralCoveringInitializedFrameAverage.program I ib ih ifreq it L Δ a B k t b n q hB).maxBits ≤
      coefficient ifreq L Δ a B k b n q c * Nat.clog 2 (N + 2) := by
  let H := Nat.clog 2 (N + 2)
  have hH : 1 ≤ H := Nat.clog_pos (by omega) (by omega)
  have hids' : ids ≤ c * H := hids
  have hi : ids + 1 ≤ (c + 1) * H := by nlinarith
  have h3 : 3 ≤ 3 * H := by omega
  have ho : ids + 3 ≤ (c + 3) * H := by nlinarith
  rw [GeneralCoveringInitializedFrameAverage.maxBits, GeneralCoveringOwnerFrameAverage.maxBits]
  apply max_le
  · apply (GeneralCoveringInitializerRun.maxBits I ib ih ifreq it).trans
    apply max_le
    · exact hi.trans (Nat.mul_le_mul_right H ((le_max_left _ _).trans (le_max_left _ _)))
    · have hb := Nat.mul_le_mul_left ifreq hi
      calc
        _ ≤ (ifreq * (c + 1)) * H := by simpa only [Nat.mul_assoc] using hb
        _ ≤ _ := Nat.mul_le_mul_right H ((le_max_right _ _).trans (le_max_left _ _))
  · apply max_le
    · exact (task_bits I L Δ a B k t b n q hB N c hids).trans
        (Nat.mul_le_mul_right H ((le_max_left _ _).trans (le_max_right _ _)))
    · exact ho.trans (Nat.mul_le_mul_right H ((le_max_right _ _).trans (le_max_right _ _)))

theorem rounds {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (GeneralCoveringInitializedFrameAverage.program I ib ih ifreq it L Δ a B k t b n q hB).rounds =
      it * (5 + 2 * ifreq) + 18 + 4 * GeneralCoveringOwnerFrameTaskInputs.outerRadius k n +
        RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) := by
  rw [GeneralCoveringInitializedFrameAverage.rounds, GeneralCoveringInitializerRun.rounds,
    GeneralCoveringOwnerFrameAverage.rounds, GeneralCoveringOwnerFrameFractional.rounds]
  omega

end Paper.GeneralCoveringFrameAverageResources

#print axioms Paper.GeneralCoveringFrameAverageResources.task_bits
#print axioms Paper.GeneralCoveringFrameAverageResources.logarithmic_bits
#print axioms Paper.GeneralCoveringFrameAverageResources.rounds
