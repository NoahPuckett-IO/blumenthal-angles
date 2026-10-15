import Blumenthal.Reduction

/-!
# The dyadic lower bound (Szekeres 1941, Erdős–Szekeres 1960)

If every angle of a finite planar set is at most `(1 - 1/n) π` (`n ≥ 2`), the set has at most
`2^n` points. Equivalently, every set of `2^n + 1` points has an angle `> (1 - 1/n) π`.

Proof: colour each pair `{p, q}` by the arc `[kπ/n, (k+1)π/n)` containing the direction of the
line `pq`, and orient it so that `q - p` points into the upper half-plane. Two consecutive
edges `p → q → r` of one colour would make `∠ p q r > (1 - 1/n) π`. So each colour class has no
paths of length two, and the map sending `p` to the set of colours in which `p` has an
in-neighbour is injective into `{0,1}^n`.

This is the case `u = 2n` of `CapacityBound`.
-/

open EuclideanGeometry InnerProductGeometry Real

namespace Blumenthal

/-- The plane, identified with `ℂ` by a linear isometry. -/
noncomputable def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

lemma angle_toC (x y : Plane) :
    InnerProductGeometry.angle (toC x) (toC y) = InnerProductGeometry.angle x y :=
  toC.toLinearIsometry.angle_map x y

/-- Nonzero complex numbers with argument in `[0, π)`. -/
def Upper (z : ℂ) : Prop := 0 < z.im ∨ (z.im = 0 ∧ 0 < z.re)

lemma Upper.ne_zero {z : ℂ} (h : Upper z) : z ≠ 0 := by
  rintro rfl
  simp [Upper] at h

lemma upper_or_upper_neg {z : ℂ} (hz : z ≠ 0) : Upper z ∨ Upper (-z) := by
  simp only [Upper, Complex.neg_im, Complex.neg_re]
  rcases lt_trichotomy z.im 0 with h | h | h
  · right; left; linarith
  · rcases lt_trichotomy z.re 0 with h' | h' | h'
    · right; right; exact ⟨by linarith, by linarith⟩
    · exact absurd (Complex.ext h' h) hz
    · left; right; exact ⟨h, h'⟩
  · left; left; exact h

lemma not_upper_and_upper_neg {z : ℂ} (h : Upper z) (h' : Upper (-z)) : False := by
  simp only [Upper, Complex.neg_im, Complex.neg_re] at h h'
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩ <;> linarith

lemma Upper.arg_nonneg {z : ℂ} (h : Upper z) : 0 ≤ Complex.arg z :=
  Complex.arg_nonneg_iff.2 (by
    rcases h with h | h
    · exact h.le
    · exact h.1.ge)

lemma Upper.arg_lt_pi {z : ℂ} (h : Upper z) : Complex.arg z < π := by
  refine lt_of_le_of_ne (Complex.arg_le_pi z) fun he => ?_
  rw [Complex.arg_eq_pi_iff] at he
  rcases h with h | h
  · linarith [he.2]
  · linarith [he.1, h.2]

lemma angle_eq_abs_sub_arg {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h : |Complex.arg z - Complex.arg w| < π) :
    InnerProductGeometry.angle z w = |Complex.arg z - Complex.arg w| := by
  rw [Complex.angle_eq_abs_arg hz hw]
  congr 1
  have e := Complex.arg_div_coe_angle hz hw
  rw [← Real.Angle.coe_sub] at e
  have := congrArg Real.Angle.toReal e
  rw [Complex.arg_coe_angle_toReal_eq_arg,
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith [(abs_lt.1 h).1], by linarith [(abs_lt.1 h).2]⟩]
    at this
  exact this

/-- The colour of a direction: the index `k` with `arg z ∈ [kπ/n, (k+1)π/n)`. -/
noncomputable def colour (n : ℕ) (z : ℂ) : ℕ := ⌊Complex.arg z * n / π⌋₊

lemma colour_lt {n : ℕ} (hn : 0 < n) {z : ℂ} (h : Upper z) : colour n z < n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [colour, Nat.floor_lt (by have := h.arg_nonneg; positivity)]
  rw [div_lt_iff₀ pi_pos]
  nlinarith [h.arg_lt_pi]

lemma abs_arg_sub_lt_of_colour_eq {n : ℕ} (hn : 0 < n) {z w : ℂ} (hz : Upper z) (hw : Upper w)
    (hc : colour n z = colour n w) : |Complex.arg z - Complex.arg w| < π / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Complex.arg z * n / π with ha
  set b := Complex.arg w * n / π with hb
  have ha0 : 0 ≤ a := by have := hz.arg_nonneg; positivity
  have hb0 : 0 ≤ b := by have := hw.arg_nonneg; positivity
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one b
  simp only [colour] at hc
  rw [← ha, ← hb] at hc
  rw [hc] at h1 h2
  have hab : |a - b| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have ez : Complex.arg z = a * π / n := by rw [ha]; field_simp
  have ew : Complex.arg w = b * π / n := by rw [hb]; field_simp
  rw [ez, ew, show a * π / n - b * π / n = (a - b) * (π / n) by ring, abs_mul,
    abs_of_pos (by positivity : 0 < π / n)]
  have : 0 < π / n := by positivity
  nlinarith

/-- **Szekeres / Erdős–Szekeres.** A planar set with all angles at most `(1 - 1/n) π` has at most
`2^n` points. -/
theorem card_le_two_pow_of_anglesLE (n : ℕ) (hn : 2 ≤ n) (A : Finset Plane)
    (h : AnglesLE A ((1 - 1 / n) * π)) : A.card ≤ 2 ^ n := by
  classical
  have hn0 : 0 < n := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- `R k p q`: the edge `p → q` has colour `k`
  let R : ℕ → Plane → Plane → Prop := fun k p q =>
    Upper (toC (q - p)) ∧ colour n (toC (q - p)) = k
  have hneg : ∀ p q : Plane, toC (p - q) = - toC (q - p) := fun p q => by
    rw [← map_neg, neg_sub]
  have chain : ∀ k, ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, R k p q → R k q r → False := by
    intro k p hp q hq r hr h1 h2
    have hpq : p ≠ q := by
      rintro rfl
      exact h1.1.ne_zero (by simp)
    have hqr : q ≠ r := by
      rintro rfl
      exact h2.1.ne_zero (by simp)
    have hpr : p ≠ r := by
      rintro rfl
      exact not_upper_and_upper_neg h1.1 (by rw [← hneg]; exact h2.1)
    have hclose := abs_arg_sub_lt_of_colour_eq hn0 h1.1 h2.1 (h1.2.trans h2.2.symm)
    have hpi : π / n ≤ π := div_le_self pi_pos.le (by linarith)
    have hang : InnerProductGeometry.angle (toC (q - p)) (toC (r - q)) < π / n := by
      rw [angle_eq_abs_sub_arg h1.1.ne_zero h2.1.ne_zero (by linarith)]
      exact hclose
    have hA := h p hp q hq r hr hpq hqr hpr
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hA
    rw [← angle_toC, hneg p q, angle_neg_left] at hA
    have e : (1 - 1 / (n : ℝ)) * π = π - π / n := by ring
    linarith
  let f : Plane → (Fin n → Bool) := fun p k => decide (∃ q ∈ A, R (k : ℕ) q p)
  have hinj : Set.InjOn f A := by
    intro p hp q hq hfe
    by_contra hne
    have hz : toC (q - p) ≠ 0 := by
      rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]
      exact sub_ne_zero.2 (Ne.symm hne)
    rcases upper_or_upper_neg hz with hu | hu
    · have hk := colour_lt hn0 hu
      have h1 : f q ⟨_, hk⟩ = true := by
        simp only [f, decide_eq_true_eq]
        exact ⟨p, hp, hu, rfl⟩
      have h2 : f p ⟨_, hk⟩ = false := by
        simp only [f, decide_eq_false_iff_not, not_exists, not_and]
        intro r hr hR
        exact chain _ r hr p hp q hq hR ⟨hu, rfl⟩
      rw [hfe, h1] at h2
      exact Bool.noConfusion h2
    · rw [← hneg] at hu
      have hk := colour_lt hn0 hu
      have h1 : f p ⟨_, hk⟩ = true := by
        simp only [f, decide_eq_true_eq]
        exact ⟨q, hq, hu, rfl⟩
      have h2 : f q ⟨_, hk⟩ = false := by
        simp only [f, decide_eq_false_iff_not, not_exists, not_and]
        intro r hr hR
        exact chain _ r hr q hq p hp hR ⟨hu, rfl⟩
      rw [← hfe, h1] at h2
      exact Bool.noConfusion h2
  calc A.card ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 2 ^ n := by simp

/-- `CapacityBound` at every even integer `u = 2n`. -/
theorem capacityBound_even (n : ℕ) (hn : 2 ≤ n) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / (2 * n : ℝ)) * π)) : A.card ≤ capacity (2 * n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfl : ⌊(2 * n : ℝ) / 2⌋₊ = n := by
    rw [show (2 * n : ℝ) / 2 = n by ring, Nat.floor_natCast]
  have hcap : capacity (2 * n) = 2 ^ n := by
    rw [capacity_of_band_one (by linarith) (by rw [hfl]; linarith), hfl]
  rw [hcap]
  apply card_le_two_pow_of_anglesLE n hn A
  have e : (1 - 2 / (2 * n : ℝ)) * π = (1 - 1 / n) * π := by
    field_simp
  rwa [← e]

/-- Every set of more than `2^n` points has an angle `> (1 - 1/n) π`; hence
`(1 - 1/n) π ≤ α_N` for `N > 2^n`. -/
theorem le_alpha_of_two_pow_lt {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ^ n < N) :
    (1 - 1 / n) * π ≤ alpha N := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 1 / (n : ℝ) := by positivity
  refine le_alpha (by nlinarith [pi_pos]) (by nlinarith [pi_pos]) fun A hA => ?_
  by_contra hno
  have hle : AnglesLE A ((1 - 1 / n) * π) := by
    intro x hx y hy z hz hxy hyz hxz
    by_contra hlt
    exact hno ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, (not_le.1 hlt).le⟩
  have := card_le_two_pow_of_anglesLE n hn A hle
  omega

end Blumenthal
