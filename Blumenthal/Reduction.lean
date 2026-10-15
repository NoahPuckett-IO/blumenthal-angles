import Blumenthal.Statement

/-!
# The lower bounds are equivalent to the capacity bound

`CapacityBound ↔ SendovLower`. So the lower-bound half of Blumenthal's problem is exactly the
statement that a planar set with all angles at most `(1 - 2/u) π` has at most `capacity u` points.
This isolates the open part of the problem as one geometric statement, proved equivalent with no
`sorry`.
-/

open EuclideanGeometry Real

namespace Blumenthal

/-! ### Arithmetic of `capacity` -/

lemma two_le_floor_half {u : ℝ} (hu : 4 ≤ u) : 2 ≤ ⌊u / 2⌋₊ :=
  Nat.le_floor (by push_cast; linarith)

lemma floor_half_le {u : ℝ} {n : ℕ} (hu : u < 2 * n + 2) : ⌊u / 2⌋₊ ≤ n := by
  rw [← Nat.lt_succ_iff, Nat.floor_lt' (Nat.succ_ne_zero n)]
  push_cast
  linarith

lemma two_mul_floor_half_le {u : ℝ} (hu : 0 ≤ u) : 2 * (⌊u / 2⌋₊ : ℝ) ≤ u := by
  have := Nat.floor_le (show 0 ≤ u / 2 by linarith)
  linarith

lemma lt_two_mul_floor_half_add_two (u : ℝ) : u < 2 * (⌊u / 2⌋₊ : ℝ) + 2 := by
  have := Nat.lt_floor_add_one (u / 2)
  linarith

lemma capacity_of_lt_three {u : ℝ} (hu : u < 3) : capacity u = 2 := by
  simp [capacity, hu]

lemma capacity_of_lt_four {u : ℝ} (h3 : 3 ≤ u) (hu : u < 4) : capacity u = 3 := by
  simp [capacity, hu, not_lt.mpr h3]

lemma capacity_le_three {u : ℝ} (hu : u < 4) : capacity u ≤ 3 := by
  rcases lt_or_ge u 3 with h | h
  · rw [capacity_of_lt_three h]; omega
  · rw [capacity_of_lt_four h hu]

lemma capacity_of_band_one {u : ℝ} (h4 : 4 ≤ u) (hu : u < 2 * (⌊u / 2⌋₊ : ℝ) + 1) :
    capacity u = 2 ^ ⌊u / 2⌋₊ := by
  simp [capacity, hu, not_lt.mpr h4, not_lt.mpr (show (3 : ℝ) ≤ u by linarith)]

lemma capacity_of_band_two {u : ℝ} (h4 : 4 ≤ u) (hu : 2 * (⌊u / 2⌋₊ : ℝ) + 1 ≤ u) :
    capacity u = 2 ^ ⌊u / 2⌋₊ + 2 ^ (⌊u / 2⌋₊ - 2) := by
  simp [capacity, not_lt.mpr hu, not_lt.mpr h4, not_lt.mpr (show (3 : ℝ) ≤ u by linarith)]

lemma two_le_capacity (u : ℝ) : 2 ≤ capacity u := by
  rcases lt_or_ge u 4 with h4 | h4
  · rcases lt_or_ge u 3 with h3 | h3
    · rw [capacity_of_lt_three h3]
    · rw [capacity_of_lt_four h3 h4]; omega
  · have hm := two_le_floor_half h4
    have : 4 ≤ 2 ^ ⌊u / 2⌋₊ := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hm)
    rcases lt_or_ge u (2 * (⌊u / 2⌋₊ : ℝ) + 1) with h | h
    · rw [capacity_of_band_one h4 h]
      exact le_trans (by norm_num) this
    · rw [capacity_of_band_two h4 h]
      exact le_trans (by norm_num) (this.trans (Nat.le_add_right _ _))

lemma pow_add_pow_sub_two_le {m : ℕ} : 2 ^ m + 2 ^ (m - 2) ≤ 2 ^ (m + 1) := by
  have : 2 ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.sub_le m 2)
  rw [pow_succ]
  omega

/-- Below `2n + 1` the capacity is at most `2^n`. -/
lemma capacity_le_of_lt_band_one {u : ℝ} {n : ℕ} (hn : 2 ≤ n) (hu : u < 2 * n + 1) :
    capacity u ≤ 2 ^ n := by
  have h4n : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hn)
  rcases lt_or_ge u 4 with h4 | h4
  · exact (capacity_le_three h4).trans (by omega)
  · have hmn : ⌊u / 2⌋₊ ≤ n := floor_half_le (by linarith)
    rcases lt_or_ge u (2 * (⌊u / 2⌋₊ : ℝ) + 1) with h | h
    · rw [capacity_of_band_one h4 h]
      exact Nat.pow_le_pow_right two_pos hmn
    · rw [capacity_of_band_two h4 h]
      have hlt : ⌊u / 2⌋₊ < n := by
        by_contra hc
        have : (n : ℝ) ≤ ⌊u / 2⌋₊ := by exact_mod_cast not_lt.mp hc
        linarith
      exact pow_add_pow_sub_two_le.trans (Nat.pow_le_pow_right two_pos hlt)

/-- Below `2n + 2` the capacity is at most `2^n + 2^(n-2)`. -/
lemma capacity_le_of_lt_band_two {u : ℝ} {n : ℕ} (hn : 2 ≤ n) (hu : u < 2 * n + 2) :
    capacity u ≤ 2 ^ n + 2 ^ (n - 2) := by
  have h4n : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hn)
  rcases lt_or_ge u 4 with h4 | h4
  · exact (capacity_le_three h4).trans (le_trans (by omega : 3 ≤ 2 ^ n) (Nat.le_add_right _ _))
  · have hmn : ⌊u / 2⌋₊ ≤ n := floor_half_le hu
    rcases lt_or_ge u (2 * (⌊u / 2⌋₊ : ℝ) + 1) with h | h
    · rw [capacity_of_band_one h4 h]
      exact (Nat.pow_le_pow_right two_pos hmn).trans (Nat.le_add_right _ _)
    · rw [capacity_of_band_two h4 h]
      exact Nat.add_le_add (Nat.pow_le_pow_right two_pos hmn)
        (Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right hmn 2))

/-! ### From the capacity bound to lower bounds for `alpha` -/

/-- Writing an angle bound `β < π` as `(1 - 2/u) π` with `u = 2π/(π - β)`. -/
lemma one_sub_two_div_mul_pi {β : ℝ} (hβ : β < π) : (1 - 2 / (2 * π / (π - β))) * π = β := by
  have hπ : 0 < π := pi_pos
  have h : π - β ≠ 0 := by linarith
  field_simp
  ring

/-- The mechanism behind every lower bound: if `capacity u < N` for all `0 < u < u₀`, the capacity
bound forces an angle `≥ (1 - 2/u₀) π` in every `N`-point set. -/
theorem le_alpha_of_capacityBound (hL : CapacityBound) {N : ℕ} (hN : 3 ≤ N) {u₀ : ℝ}
    (hu₀ : 2 ≤ u₀) (hcap : ∀ u : ℝ, 0 < u → u < u₀ → capacity u < N) :
    (1 - 2 / u₀) * π ≤ alpha N := by
  have hπ : 0 < π := pi_pos
  have hu₀pos : 0 < u₀ := by linarith
  have h2u : 2 / u₀ ≤ 1 := (div_le_one hu₀pos).mpr hu₀
  have h2u0 : 0 < 2 / u₀ := by positivity
  refine le_alpha (by nlinarith) (by nlinarith) fun A hA => ?_
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hmax⟩ := exists_max_angle (hA ▸ hN)
  refine ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, ?_⟩
  by_contra! hlt
  have hβπ : ∠ x y z < π := by nlinarith
  have hβ0 : 0 ≤ ∠ x y z := angle_nonneg x y z
  have hden : 0 < π - ∠ x y z := by linarith
  have hu : 0 < 2 * π / (π - ∠ x y z) := by positivity
  have huu : 2 * π / (π - ∠ x y z) < u₀ := by
    rw [div_lt_iff₀ hden]
    have : 2 / u₀ * π < π - ∠ x y z := by nlinarith
    calc 2 * π = u₀ * (2 / u₀ * π) := by field_simp
      _ < u₀ * (π - ∠ x y z) := by gcongr
  have hcard := hL _ hu A (by rw [one_sub_two_div_mul_pi hβπ]; exact hmax)
  have := hcap _ hu huu
  omega

theorem sendovLower_of_capacityBound (hL : CapacityBound) : SendovLower := by
  refine ⟨?_, ?_, fun n N hn h1 h2 => ?_⟩
  · have := le_alpha_of_capacityBound hL le_rfl (show (2 : ℝ) ≤ 3 by norm_num)
      fun u _ hu => by rw [capacity_of_lt_three hu]; omega
    convert this using 1
    ring
  · have := le_alpha_of_capacityBound hL (show 3 ≤ 4 by norm_num) (show (2 : ℝ) ≤ 4 by norm_num)
      fun u _ hu => (capacity_le_three hu).trans_lt (by norm_num)
    convert this using 1
    ring
  · have h4n : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hn)
    have hN : 3 ≤ N := by omega
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold bandValue
    split_ifs with hband
    · exact le_alpha_of_capacityBound hL hN (by linarith)
        fun u _ hu => (capacity_le_of_lt_band_one hn hu).trans_lt h1
    · have := le_alpha_of_capacityBound hL hN (show (2 : ℝ) ≤ 2 * n + 2 by linarith)
        fun u _ hu => (capacity_le_of_lt_band_two hn hu).trans_lt (by omega)
      convert this using 2
      field_simp

/-! ### From lower bounds for `alpha` back to the capacity bound -/

theorem capacityBound_of_sendovLower (hS : SendovLower) : CapacityBound := by
  obtain ⟨l3, l4, l⟩ := hS
  intro u hu A hA
  by_contra! hgt
  have hπ : 0 < π := pi_pos
  have hcap2 := two_le_capacity u
  -- an `N₀`-point set with `N₀ = capacity u + 1 ≤ A.card` has an angle above `(1 - 2/u) π`
  set N₀ := capacity u + 1 with hN₀
  have hN₀3 : 3 ≤ N₀ := by omega
  have hA3 : 3 ≤ A.card := by omega
  -- the bound in `hA` is nonnegative, since `A` has some angle
  have hb0 : 0 ≤ (1 - 2 / u) * π := by
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, -⟩ := exists_max_angle hA3
    exact (angle_nonneg x y z).trans (hA x hx y hy z hz hxy hyz hxz)
  have hup : alpha A.card ≤ (1 - 2 / u) * π := alpha_le hb0 rfl hA
  have hmono : alpha N₀ ≤ alpha A.card := alpha_mono hN₀3 (by omega)
  -- `alpha N₀` exceeds `(1 - 2/u) π`
  have key : (1 - 2 / u) * π < alpha N₀ := by
    rcases lt_or_ge u 4 with h4 | h4
    · rcases lt_or_ge u 3 with h3 | h3
      · have hN : N₀ = 3 := by rw [hN₀, capacity_of_lt_three h3]
        rw [hN]
        refine lt_of_lt_of_le ?_ l3
        have : 2 / 3 < 2 / u := by gcongr
        nlinarith
      · have hN : N₀ = 4 := by rw [hN₀, capacity_of_lt_four h3 h4]
        rw [hN]
        refine lt_of_lt_of_le ?_ l4
        have : 2 / 4 < 2 / u := by gcongr
        nlinarith
    · set m := ⌊u / 2⌋₊ with hm
      have hm2 : 2 ≤ m := two_le_floor_half h4
      have h4m : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hm2)
      have h1m : 1 ≤ 2 ^ (m - 2) := Nat.one_le_two_pow
      have hsub : 2 ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.sub_le m 2)
      have hupper : u < 2 * (m : ℝ) + 2 := lt_two_mul_floor_half_add_two u
      have hpow : 2 ^ (m - 2) * 4 = 2 ^ m := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hm2]
      rcases lt_or_ge u (2 * (m : ℝ) + 1) with hb | hb
      · have hN : N₀ = 2 ^ m + 1 := by rw [hN₀, capacity_of_band_one h4 hb]
        have hval := l m N₀ hm2 (by omega) (by rw [hN, pow_succ]; omega)
        have hc : N₀ ≤ 2 ^ m + 2 ^ (m - 2) := by omega
        unfold bandValue at hval
        simp only [hc, ↓reduceIte] at hval
        refine lt_of_lt_of_le ?_ hval
        have : 2 / (2 * (m : ℝ) + 1) < 2 / u := by gcongr
        nlinarith
      · have hN : N₀ = 2 ^ m + 2 ^ (m - 2) + 1 := by rw [hN₀, capacity_of_band_two h4 hb]
        have hval := l m N₀ hm2 (by omega) (by rw [hN, pow_succ]; omega)
        have hc : ¬ N₀ ≤ 2 ^ m + 2 ^ (m - 2) := by omega
        unfold bandValue at hval
        simp only [hc, ↓reduceIte] at hval
        refine lt_of_lt_of_le ?_ hval
        have : 1 / ((m : ℝ) + 1) < 2 / u := by
          rw [div_lt_div_iff₀ (by positivity) (by linarith)]
          linarith
        nlinarith
  linarith

/-- **The lower-bound half of Blumenthal's problem is equivalent to the capacity bound.** -/
theorem capacityBound_iff_sendovLower : CapacityBound ↔ SendovLower :=
  ⟨sendovLower_of_capacityBound, capacityBound_of_sendovLower⟩

/-- Consequently the full answer is equivalent to the capacity bound together with the
upper bounds (Sendov's constructions). -/
theorem sendovAnswer_iff_capacityBound_and_upper :
    SendovAnswer ↔ CapacityBound ∧ SendovUpper := by
  rw [sendovAnswer_iff, capacityBound_iff_sendovLower]

end Blumenthal
