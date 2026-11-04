import Blumenthal.FirstBand
import Blumenthal.N4.Reduce3

/-!
# α_N = 7π/9 for 17 ≤ N ≤ 20

The first band of `CapacityBound` for `n = 4` (`8 ≤ u < 9`) from `N4.statementR_four`, and the
resulting exact values, exactly as `alpha_nine` / `alpha_ten` in `FirstBand.lean`.
-/

open Real

namespace Blumenthal

/-- `CapacityBound` for `8 ≤ u < 9`, from (R) for `n = 4`. -/
theorem capacityBound_eight_nine {u : ℝ} (hu : 8 ≤ u) (hu' : u < 9) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / u) * π)) : A.card ≤ capacity u :=
  capacityBound_firstBand_of_statementR (by norm_num) N4.statementR_four
    (by push_cast; linarith) (by push_cast; linarith) A hA

lemma alpha_seventeen_twenty_lower {N : ℕ} (hN : 17 ≤ N) : 7 * π / 9 ≤ alpha N := by
  have := le_alpha_of_card_lt (N := N) (by omega) (u₁ := 8) (u₀ := 9) (by norm_num)
    (by norm_num) (fun u hu hu' A hA => by
      have h := capacityBound_eight_nine hu hu' A hA
      rw [capacity_of_band_one (by linarith)
        (by rw [floor_half_eq (n := 4) (by push_cast; linarith) (by push_cast; linarith)];
            push_cast; linarith),
        floor_half_eq (n := 4) (by push_cast; linarith) (by push_cast; linarith)] at h
      have : (2 : ℕ) ^ 4 = 16 := by norm_num
      omega)
  convert this using 1
  ring

lemma alpha_seventeen_twenty_upper {N : ℕ} (h17 : 17 ≤ N) (h20 : N ≤ 20) :
    alpha N ≤ 7 * π / 9 := by
  have := sendovUpper.2.2 4 N (by norm_num) (by norm_num; omega) (by norm_num; omega)
  rw [bandValue, if_pos (by norm_num; omega)] at this
  convert this using 1
  push_cast
  ring

/-- **`α_N = 7π/9` for `17 ≤ N ≤ 20`.** -/
theorem alpha_seventeen_to_twenty {N : ℕ} (h17 : 17 ≤ N) (h20 : N ≤ 20) :
    alpha N = 7 * π / 9 :=
  le_antisymm (alpha_seventeen_twenty_upper h17 h20) (alpha_seventeen_twenty_lower h17)

end Blumenthal
